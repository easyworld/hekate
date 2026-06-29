/*
 * Copyright (c) 2018 naehrwert
 * Copyright (c) 2018 Rajko Stojadinovic
 * Copyright (c) 2018-2026 CTCaer
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms and conditions of the GNU General Public License,
 * version 2, as published by the Free Software Foundation.
 *
 * This program is distributed in the hope it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
 * more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

//! fix the dram stuff and the pop ups

#include <string.h>
#include <stdlib.h>

#include <bdk.h>

#include "gui.h"
#include "fe_emmc_tools.h"
#include "fe_emummc_tools.h"
#include "../config.h"
#include <libs/fatfs/ff.h>

#define VERIF_STATUS_OK    0
#define VERIF_STATUS_ERROR 1
#define VERIF_STATUS_ABORT 2

#define NUM_SECTORS_PER_ITER 8192 // 4MB Cache.
#define OUT_FILENAME_SZ 128
#define HASH_FILENAME_SZ (OUT_FILENAME_SZ + 11) // 11 == strlen(".sha256sums")

extern nyx_config n_cfg;

extern char *emmcsn_path_impl(char *path, char *sub_dir, char *filename, sdmmc_storage_t *storage);

static void _get_valid_partition(u32 *sector_start, u32 *sector_size, u32 *part_idx, bool backup)
{
	sd_mount();
	mbr_t *mbr = (mbr_t *)zalloc(sizeof(mbr_t));
	sdmmc_storage_read(&sd_storage, 0, 1, mbr);

	*part_idx = 0;
	int i = 0;
	u32 curr_part_size = 0;
	// Find first partition with emuMMC GPP.
	for (i = 1; i < 4; i++)
	{
		curr_part_size = mbr->partitions[i].size_sct;
		*sector_start = mbr->partitions[i].start_sct;
		u8 type = mbr->partitions[i].type;
		u32 sector_size_safe = backup ? 0x400000 : (*sector_size) + 0x8000; // 2GB min safe size for backup.
		if ((curr_part_size >= sector_size_safe) && (*sector_start) && type != 0x83 && (!backup || type == 0xE0))
		{
			if (backup)
			{
				u8 gpt_check[SD_BLOCKSIZE] = { 0 };
				sdmmc_storage_read(&sd_storage, (*sector_start) + 0xC001, 1, gpt_check);
				if (!memcmp(gpt_check, "EFI PART", 8))
				{
					*sector_size = curr_part_size;
					*sector_start = (*sector_start) + 0x8000;
					break;
				}
				sdmmc_storage_read(&sd_storage, (*sector_start) + 0x4001, 1, gpt_check);
				if (!memcmp(gpt_check, "EFI PART", 8))
				{
					*sector_size = curr_part_size;
					break;
				}
			}
			else
				break;
		}
	}
	free(mbr);

	if (i < 4)
		*part_idx = i;
	else
	{
		*sector_start = 0;
		*sector_size = 0;
		*part_idx = 0;
	}

	// Get emuMMC GPP size.
	if (backup && *part_idx && *sector_size)
	{
		gpt_t *gpt = (gpt_t *)zalloc(sizeof(gpt_t));
		sdmmc_storage_read(&sd_storage, (*sector_start) + 0x4001, 1, gpt);

		u32 new_size = gpt->header.alt_lba + 1;
		if (*sector_size > new_size)
			*sector_size = new_size;
		else
			*sector_size = 0;

		free(gpt);
	}
	else if (!backup && *part_idx)
		*sector_start = (*sector_start) + 0x8000;
}

static lv_obj_t *create_mbox_text(const char *text, bool button_ok)
{
	lv_obj_t *dark_bg = lv_obj_create(lv_scr_act(), NULL);
	lv_obj_set_style(dark_bg, &mbox_darken);
	lv_obj_set_size(dark_bg, LV_HOR_RES, LV_VER_RES);

	static const char *mbox_btn_map[] = { "\251", "\222确定", "\251", "" };
	lv_obj_t *mbox = lv_mbox_create(dark_bg, NULL);
	lv_mbox_set_recolor_text(mbox, true);
	lv_obj_set_width(mbox, LV_HOR_RES / 9 * 6);

	lv_mbox_set_text(mbox, text);
	if (button_ok)
		lv_mbox_add_btns(mbox, mbox_btn_map, nyx_mbox_action);

	lv_obj_align(mbox, NULL, LV_ALIGN_CENTER, 0, 0);
	lv_obj_set_top(mbox, true);

	return dark_bg;
}

static void _update_filename(char *outFilename, u32 sdPathLen, u32 currPartIdx)
{
	if (currPartIdx < 10)
	{
		outFilename[sdPathLen] = '0';
		itoa(currPartIdx, &outFilename[sdPathLen + 1], 10);
	}
	else
		itoa(currPartIdx, &outFilename[sdPathLen], 10);
}

static int _emmc_sd_copy_verify(emmc_tool_gui_t *gui, sdmmc_storage_t *storage, u32 lba_curr, const char *outFilename, const emmc_part_t *part)
{
	FIL fp;
	FIL hashFp;
	u8 sparseShouldVerify = 4;
	u32 prevPct = 200;
	u32 sdFileSector = 0;
	int res = 0;
	static const char hexa[] = "0123456789abcdef";
	DWORD *clmt = NULL;

	u8 hashEm[SE_SHA_256_SIZE];
	u8 hashSd[SE_SHA_256_SIZE];

	if (f_open(&fp, outFilename, FA_READ) == FR_OK)
	{
		if (n_cfg.verification == 3)
		{
			char hashFilename[HASH_FILENAME_SZ];
			strncpy(hashFilename, outFilename, OUT_FILENAME_SZ - 1);
			strcat(hashFilename, ".sha256sums");

			res = f_open(&hashFp, hashFilename, FA_CREATE_ALWAYS | FA_WRITE);
			if (res)
			{
				f_close(&fp);

				s_printf(gui->txt_buf,
						"\n#FF0000 无法写入哈希文件(错误%d)!#\n"
						"#FF0000 正在中止..#\n", res);
				lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
				manual_system_maintenance(true);

				return VERIF_STATUS_ERROR;
			}

			char chunkSizeAscii[10];
			itoa(NUM_SECTORS_PER_ITER * EMMC_BLOCKSIZE, chunkSizeAscii, 10);
			chunkSizeAscii[9] = '\0';

			f_puts("# chunksize: ", &hashFp);
			f_puts(chunkSizeAscii, &hashFp);
			f_puts("\n", &hashFp);
		}

		u32 totalSectorsVer = (u32)((u64)f_size(&fp) >> (u64)9);

		u8 *bufEm = (u8 *)EMMC_BUF_ALIGNED;
		u8 *bufSd = (u8 *)SDXC_BUF_ALIGNED;

		u32 pct = (u64)((u64)(lba_curr - part->lba_start) * 100u) / (u64)(part->lba_end - part->lba_start);
		lv_bar_set_value(gui->bar, pct);
		lv_bar_set_style(gui->bar, LV_BAR_STYLE_BG, gui->bar_teal_bg);
		lv_bar_set_style(gui->bar, LV_BAR_STYLE_INDIC, gui->bar_teal_ind);
		s_printf(gui->txt_buf, " "SYMBOL_DOT" %d%%", pct);
		lv_label_set_text(gui->label_pct, gui->txt_buf);
		manual_system_maintenance(true);

		clmt = f_expand_cltbl(&fp, SZ_4M, 0);

		u32 num = 0;
		while (totalSectorsVer > 0)
		{
			num = MIN(totalSectorsVer, NUM_SECTORS_PER_ITER);

			// Check every time or every 4.
			// Every 4 protects from fake sd, sector corruption and frequent I/O corruption.
			// Full provides all that, plus protection from extremely rare I/O corruption.
			if ((n_cfg.verification >= 2) || !(sparseShouldVerify % 4))
			{
				if (sdmmc_storage_read(storage, lba_curr, num, bufEm))
				{
					s_printf(gui->txt_buf,
						"\n#FF0000 无法读取eMMC中的%d个块(@LBA %08X),#\n"
						"#FF0000 校验失败..#\n",
						num, lba_curr);
					lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
					manual_system_maintenance(true);

					free(clmt);
					f_close(&fp);
					if (n_cfg.verification == 3)
						f_close(&hashFp);

					return VERIF_STATUS_ERROR;
				}
				manual_system_maintenance(false);

				se_sha_hash_256_async(hashEm, bufEm, num << 9);

				f_lseek(&fp, (u64)sdFileSector << (u64)9);
				if (f_read_fast(&fp, bufSd, num << 9))
				{
					s_printf(gui->txt_buf,
						"\n#FF0000 无法读取SD卡中的%d个块(@LBA %08X),#\n"
						"#FF0000 校验失败..#\n",
						num, lba_curr);
					lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
					manual_system_maintenance(true);

					free(clmt);
					f_close(&fp);
					if (n_cfg.verification == 3)
						f_close(&hashFp);

					return VERIF_STATUS_ERROR;
				}
				manual_system_maintenance(false);
				se_sha_hash_256_finalize(hashEm);
				se_sha_hash_256_oneshot(hashSd, bufSd, num << 9);
				res = memcmp(hashEm, hashSd, SE_SHA_256_SIZE / 2);

				if (res)
				{
					s_printf(gui->txt_buf,
						"\n#FF0000 SD卡和eMMC数据(@LBA %08X)不匹配!#\n"
						"\n#FF0000 校验失败..#\n",
						lba_curr);
					lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
					manual_system_maintenance(true);

					free(clmt);
					f_close(&fp);
					if (n_cfg.verification == 3)
						f_close(&hashFp);

					return VERIF_STATUS_ERROR;
				}

				if (n_cfg.verification == 3)
				{
					// Transform computed hash to readable hexadecimal
					char hashStr[SE_SHA_256_SIZE * 2 + 1];
					char *hashStrPtr = hashStr;
					for (int i = 0; i < SE_SHA_256_SIZE; i++)
					{
						*(hashStrPtr++) = hexa[hashSd[i] >> 4];
						*(hashStrPtr++) = hexa[hashSd[i] & 0x0F];
					}
					hashStr[SE_SHA_256_SIZE * 2] = '\0';

					f_puts(hashStr, &hashFp);
					f_puts("\n", &hashFp);
				}
			}

			pct = (u64)((u64)(lba_curr - part->lba_start) * 100u) / (u64)(part->lba_end - part->lba_start);
			if (pct != prevPct)
			{
				lv_bar_set_value(gui->bar, pct);
				s_printf(gui->txt_buf, " "SYMBOL_DOT" %d%%", pct);
				lv_label_set_text(gui->label_pct, gui->txt_buf);
				manual_system_maintenance(true);
				prevPct = pct;
			}

			manual_system_maintenance(false);

			lba_curr += num;
			totalSectorsVer -= num;
			sdFileSector += num;
			sparseShouldVerify++;

			// Check for cancellation combo.
			if (btn_read_vol() == (BTN_VOL_UP | BTN_VOL_DOWN))
			{
				strcpy(gui->txt_buf, "#FFDD00 校验已取消!#\n");
				lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
				manual_system_maintenance(true);

				msleep(1000);

				free(clmt);
				f_close(&fp);
				f_close(&hashFp);

				return VERIF_STATUS_ABORT;
			}
		}
		free(clmt);
		f_close(&fp);
		f_close(&hashFp);

		lv_bar_set_value(gui->bar, pct);
		s_printf(gui->txt_buf, " "SYMBOL_DOT" %d%%", pct);
		lv_label_set_text(gui->label_pct, gui->txt_buf);
		manual_system_maintenance(true);

		return VERIF_STATUS_OK;
	}
	else
	{
		strcpy(gui->txt_buf, "\n#FFDD00 未找到文件或无法加载!#\n#FFDD00 校验失败..#\n");
		lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
		manual_system_maintenance(true);

		return VERIF_STATUS_ERROR;
	}
}

bool partial_sd_full_unmount = false;

static int _dump_emmc_part(emmc_tool_gui_t *gui, char *sd_path, int active_part, sdmmc_storage_t *storage, emmc_part_t *part)
{
	static const u32 FAT32_FILESIZE_LIMIT = 0xFFFFFFFF;
	static const u32 SECTORS_TO_MIB_COEFF = 11;

	partial_sd_full_unmount = false;

	u32 verification = n_cfg.verification;
	u32 multipartSplitSize = (1u << 31);
	u32 lba_end = part->lba_end;
	u32 totalSectors = part->lba_end - part->lba_start + 1;
	u32 currPartIdx = 0;
	u32 numSplitParts = 0;
	u32 maxSplitParts = 0;
	bool isSmallSdCard = false;
	bool partialDumpInProgress = false;
	int res = 0;
	char *outFilename = sd_path;
	u32 sdPathLen = strlen(sd_path);

	u32 sector_start = 0, part_idx = 0;
	u32 sector_size = totalSectors;
	u32 sd_sector_off = 0;

	FIL partialIdxFp;
	char partialIdxFilename[12];
	strcpy(partialIdxFilename, "partial.idx");

	if (gui->raw_emummc)
	{
		_get_valid_partition(&sector_start, &sector_size, &part_idx, true);
		if (!part_idx || !sector_size)
		{
			strcpy(gui->txt_buf, "\n#FFDD00 未找到分区...#\n");
			lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
			manual_system_maintenance(true);

			return 1;
		}
		sd_sector_off = sector_start + (0x2000 * active_part);
		if (active_part == 2)
		{
			// Set new total sectors and lba end sector for percentage calculations.
			totalSectors = sector_size;
			lba_end = sector_size + part->lba_start - 1;
		}
	}

	s_printf(gui->txt_buf, "#96FF00 SD卡剩余空间:# %d MiB\n#96FF00 备份总大小:# %d MiB\n\n",
		(u32)(sd_fs.free_clst * sd_fs.csize >> SECTORS_TO_MIB_COEFF),
		totalSectors >> SECTORS_TO_MIB_COEFF);
	lv_label_ins_text(gui->label_info, LV_LABEL_POS_LAST, gui->txt_buf);
	manual_system_maintenance(true);

	lv_bar_set_value(gui->bar, 0);
	lv_label_set_text(gui->label_pct, " "SYMBOL_DOT" 0%");
	lv_bar_set_style(gui->bar, LV_BAR_STYLE_BG, gui->bar_white_bg);
	lv_bar_set_style(gui->bar, LV_BAR_STYLE_INDIC, gui->bar_white_ind);
	manual_system_maintenance(true);

	// 1GB parts for sd cards 8GB and less.
	if ((sd_storage.csd.capacity >> (20 - sd_storage.csd.read_blkbits)) <= 8192)
		multipartSplitSize = (1u << 30);
	// Maximum parts fitting the free space available.
	maxSplitParts = (sd_fs.free_clst * sd_fs.csize) / (multipartSplitSize / EMMC_BLOCKSIZE);

	// Check if the USER partition or the RAW eMMC fits the sd card free space.
	if (totalSectors > (sd_fs.free_clst * sd_fs.csize))
	{
		isSmallSdCard = true;

		strcpy(gui->txt_buf, "\n#FFBA00 可用空间小于备份大小.#\n");
		lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
		manual_system_maintenance(true);

		if (!maxSplitParts)
		{
			strcpy(gui->txt_buf, "#FFDD00 可用空间不足, 无法进行分卷备份!#\n");
			lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
			manual_system_maintenance(true);

			return 1;
		}
	}
	// Check if we are continuing a previous raw eMMC or USER partition backup in progress.
	if (f_open(&partialIdxFp, partialIdxFilename, FA_READ) == FR_OK && totalSectors > (FAT32_FILESIZE_LIMIT / EMMC_BLOCKSIZE))
	{
		strcpy(gui->txt_buf, "\n#AEFD14 分卷备份正在进行. 继续...#\n");
		lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
		manual_system_maintenance(true);

		partialDumpInProgress = true;
		// Force partial dumping, even if the card is larger.
		isSmallSdCard = true;

		f_read(&partialIdxFp, &currPartIdx, 4, NULL);
		f_close(&partialIdxFp);

		if (!maxSplitParts)
		{
			strcpy(gui->txt_buf, "\n#FFDD00 可用空间不足, 无法进行分卷备份!#\n");
			lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
			manual_system_maintenance(true);

			return 1;
		}

		// Increase maxSplitParts to accommodate previously backed up parts.
		maxSplitParts += currPartIdx;
	}
	else if (isSmallSdCard)
	{
		s_printf(gui->txt_buf, "\n#FFBA00 已启用分卷备份 (%d MiB分卷)...#\n", multipartSplitSize >> 20);
		lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
		manual_system_maintenance(true);
	}

	// Check if filesystem is FAT32 or the free space is smaller and backup in parts.
	if (((sd_fs.fs_type != FS_EXFAT) && totalSectors > (FAT32_FILESIZE_LIMIT / EMMC_BLOCKSIZE)) || isSmallSdCard)
	{
		u32 multipartSplitSectors = multipartSplitSize / EMMC_BLOCKSIZE;
		numSplitParts = (totalSectors + multipartSplitSectors - 1) / multipartSplitSectors;

		outFilename[sdPathLen++] = '.';

		// Continue from where we left, if Partial Backup in progress.
		_update_filename(outFilename, sdPathLen, partialDumpInProgress ? currPartIdx : 0);
	}

	FIL fp;
	if (!f_open(&fp, outFilename, FA_READ))
	{
		f_close(&fp);

		lv_obj_t *warn_mbox_bg = create_mbox_text(
			"#FFDD00 检测到已存在的备份!#\n\n"
			"按 #FF8000 电源键# 继续.\n按 #FF8000 音量键# 中断.", false);
		manual_system_maintenance(true);

		if (!(btn_wait() & BTN_POWER))
		{
			lv_obj_del(warn_mbox_bg);
			return 1;
		}
		lv_obj_del(warn_mbox_bg);
	}

	s_printf(gui->txt_buf, "#96FF00 文件路径:#\n%s\n#96FF00 文件名:# #FF8000 %s#",
		gui->base_path, outFilename + strlen(gui->base_path));
	lv_label_ins_text(gui->label_info, LV_LABEL_POS_LAST, gui->txt_buf);
	manual_system_maintenance(true);

	res = f_open(&fp, outFilename, FA_CREATE_ALWAYS | FA_WRITE);
	if (res)
	{
		s_printf(gui->txt_buf, "\n#FF0000 创建文件时出错 (%d) #\n#FFDD00 %s#\n", res, outFilename);
		lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
		manual_system_maintenance(true);

		return 1;
	}

	u8 *buf = (u8 *)MIXD_BUF_ALIGNED;

	u32 lba_curr = part->lba_start;
	u32 lbaStartPart = part->lba_start;
	u32 bytesWritten = 0;
	u32 prevPct = 200;
	int retryCount = 0;
	DWORD *clmt = NULL;

	// Continue from where we left, if Partial Backup in progress.
	if (partialDumpInProgress)
	{
		lba_curr += currPartIdx * (multipartSplitSize / EMMC_BLOCKSIZE);
		totalSectors -= currPartIdx * (multipartSplitSize / EMMC_BLOCKSIZE);
		lbaStartPart = lba_curr; // Update the start LBA for verification.
	}
	u64 totalSize = (u64)((u64)totalSectors << 9);
	if (!isSmallSdCard && (sd_fs.fs_type == FS_EXFAT || totalSize <= FAT32_FILESIZE_LIMIT))
		clmt = f_expand_cltbl(&fp, SZ_4M, totalSize);
	else
		clmt = f_expand_cltbl(&fp, SZ_4M, MIN(totalSize, multipartSplitSize));

	u32 num = 0;
	u32 pct = 0;

	lv_obj_set_opa_scale(gui->bar, LV_OPA_COVER);
	lv_obj_set_opa_scale(gui->label_pct, LV_OPA_COVER);
	while (totalSectors > 0)
	{
		if (numSplitParts != 0 && bytesWritten >= multipartSplitSize)
		{
			f_close(&fp);
			free(clmt);
			memset(&fp, 0, sizeof(fp));
			currPartIdx++;

			if (verification && !gui->raw_emummc)
			{
				// Verify part.
				res = _emmc_sd_copy_verify(gui, storage, lbaStartPart, outFilename, part);
				switch (res)
				{
				case VERIF_STATUS_OK:
					break;
				case VERIF_STATUS_ERROR:
					strcpy(gui->txt_buf, "\n#FFDD00 请重试...#\n");
					lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
					manual_system_maintenance(true);
					return 1;
				case VERIF_STATUS_ABORT:
					verification = 0;
					break;
				}

				lv_bar_set_style(gui->bar, LV_BAR_STYLE_BG, gui->bar_white_bg);
				lv_bar_set_style(gui->bar, LV_BAR_STYLE_INDIC, gui->bar_white_ind);
			}

			_update_filename(outFilename, sdPathLen, currPartIdx);

			// Always create partial.idx before next part, in case a fatal error occurs.
			if (isSmallSdCard)
			{
				// Create partial backup index file.
				if (f_open(&partialIdxFp, partialIdxFilename, FA_CREATE_ALWAYS | FA_WRITE) == FR_OK)
				{
					f_write(&partialIdxFp, &currPartIdx, 4, NULL);
					f_close(&partialIdxFp);
				}
				else
				{
					strcpy(gui->txt_buf, "\n#FF0000 创建partial.idx文件时出错!#\n");
					lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
					manual_system_maintenance(true);

					return 1;
				}

				// More parts to backup that do not currently fit the sd card free space or fatal error.
				if (currPartIdx >= maxSplitParts)
				{
					create_mbox_text(
						"#96FF00 分卷备份正在进行!#\n\n"
						"#96FF00 1.# 点击OK卸载SD卡.\n"
						"#96FF00 2.# 取出SD卡并将文件移到有可用空间的位置.\n"
						"#FFDD00 请勿移动partial.idx文件!#\n"
						"#96FF00 3.# 重新插入SD卡.\n"
						"#96FF00 4.# 再次选择相同选项以继续.", true);

					partial_sd_full_unmount = true;

					return 0;
				}
			}

			// Create next part.
			s_printf(gui->txt_buf, "%s#", outFilename + strlen(gui->base_path));
			lv_label_cut_text(gui->label_info,
				lv_txt_get_encoded_length(lv_label_get_text(gui->label_info)) - strlen(outFilename + strlen(gui->base_path)) - 1,
				strlen(outFilename + strlen(gui->base_path)) + 1);
			lv_label_ins_text(gui->label_info, LV_LABEL_POS_LAST, gui->txt_buf);
			manual_system_maintenance(true);
			lbaStartPart = lba_curr;
			res = f_open(&fp, outFilename, FA_CREATE_ALWAYS | FA_WRITE);
			if (res)
			{
				s_printf(gui->txt_buf, "\n#FF0000 创建文件时出错 (%d) #\n#FFDD00 %s#\n", res, outFilename);
				lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
				manual_system_maintenance(true);

				return 1;
			}

			bytesWritten = 0;

			totalSize = (u64)((u64)totalSectors << 9);
			clmt = f_expand_cltbl(&fp, SZ_4M, MIN(totalSize, multipartSplitSize));
		}

		retryCount = 0;
		num = MIN(totalSectors, NUM_SECTORS_PER_ITER);

		int res_read;
		if (!gui->raw_emummc)
			res_read = sdmmc_storage_read(storage, lba_curr, num, buf);
		else
			res_read = sdmmc_storage_read(&sd_storage, lba_curr + sd_sector_off, num, buf);

		while (res_read)
		{
			if (!gui->raw_emummc)
			{
				s_printf(gui->txt_buf,
					"\n#FFDD00 从eMMC读取%d个块时出错,#\n"
					"#FFDD00 LBA为%08X, (第%d次重试).#",
					num, lba_curr, ++retryCount);
			}
			else
			{
				s_printf(gui->txt_buf,
					"\n#FFDD00 从emuMMC读取%d个块时出错, LBA %08X,#\n"
					"#FFDD00 emuMMC %08X (第%d次重试).#",
					num, lba_curr + sd_sector_off, lba_curr, ++retryCount);
			}
			lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
			manual_system_maintenance(true);

			msleep(150);
			if (retryCount >= 3)
			{
				strcpy(gui->txt_buf, "#FF0000 操作已中止...#\n请重试...\n");
				lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
				manual_system_maintenance(true);

				f_close(&fp);
				free(clmt);
				f_unlink(outFilename);

				return 1;
			}
			else
			{
				strcpy(gui->txt_buf, "#FFDD00 重试中...#\n");
				lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
				manual_system_maintenance(true);
			}

			if (!gui->raw_emummc)
				res_read = sdmmc_storage_read(storage, lba_curr, num, buf);
			else
				res_read = sdmmc_storage_read(&sd_storage, lba_curr + sd_sector_off, num, buf);
			manual_system_maintenance(false);
		}

		res = f_write_fast(&fp, buf, EMMC_BLOCKSIZE * num);

		if (res)
		{
			s_printf(gui->txt_buf, "\n#FF0000 写入SD卡时发生严重错误(%d)#\n请重试...\n", res);
			lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
			manual_system_maintenance(true);

			f_close(&fp);
			free(clmt);
			f_unlink(outFilename);

			return 1;
		}

		manual_system_maintenance(false);

		pct = (u64)((u64)(lba_curr - part->lba_start) * 100u) / (u64)(lba_end - part->lba_start);
		if (pct != prevPct)
		{
			lv_bar_set_value(gui->bar, pct);
			s_printf(gui->txt_buf, " "SYMBOL_DOT" %d%%", pct);
			lv_label_set_text(gui->label_pct, gui->txt_buf);
			manual_system_maintenance(true);
			prevPct = pct;
		}

		lba_curr += num;
		totalSectors -= num;
		bytesWritten += num * EMMC_BLOCKSIZE;

		// Force a flush after a lot of data if not splitting.
		if (numSplitParts == 0 && bytesWritten >= multipartSplitSize)
		{
			f_sync(&fp);
			bytesWritten = 0;
		}

		// Check for cancellation combo.
		if (btn_read_vol() == (BTN_VOL_UP | BTN_VOL_DOWN))
		{
			strcpy(gui->txt_buf, "\n#FFDD00 备份已取消!#\n");
			lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
			manual_system_maintenance(true);

			msleep(1500);

			f_close(&fp);
			free(clmt);
			f_unlink(outFilename);

			return 1;
		}
	}
	lv_bar_set_value(gui->bar, 100);
	lv_label_set_text(gui->label_pct, " "SYMBOL_DOT" 100%");
	manual_system_maintenance(true);

	// Backup operation ended successfully.
	f_close(&fp);
	free(clmt);

	if (verification && !gui->raw_emummc)
	{
		// Verify last part or single file backup.
		if (_emmc_sd_copy_verify(gui, storage, lbaStartPart, outFilename, part) == VERIF_STATUS_ERROR)
		{
			strcpy(gui->txt_buf, "\n#FFDD00 请重试...#\n");
			lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
			manual_system_maintenance(true);

			return 1;
		}
		lv_bar_set_value(gui->bar, 100);
		lv_label_set_text(gui->label_pct, " "SYMBOL_DOT" 100%");
		manual_system_maintenance(true);
	}

	// Remove partial backup index file if no fatal errors occurred.
	if (isSmallSdCard)
	{
		f_unlink(partialIdxFilename);

		create_mbox_text(
			"#96FF00 分卷备份完成!#\n\n"
			"如果需要, 您现在可以将文件合并\n以获取完整的eMMC RAW GPP备份.", true);

		partial_sd_full_unmount = true;
	}

	return 0;
}

void dump_emmc_selected(emmcPartType_t dumpType, emmc_tool_gui_t *gui)
{
	int res = 1;
	u32 timer = 0;

	char *txt_buf = (char *)malloc(SZ_16K);
	gui->txt_buf = txt_buf;

	txt_buf[0] = 0;
	lv_label_set_text(gui->label_log, txt_buf);

	lv_label_set_text(gui->label_info, "正在检查可用空间...");
	manual_system_maintenance(true);

	if (sd_mount())
	{
		lv_label_set_text(gui->label_info, "#FFDD00 初始化SD卡失败!#");
		goto out;
	}

	// Get SD Card free space for Partial Backup.
	f_getfree("", &sd_fs.free_clst, NULL);

	if (emmc_initialize(false))
	{
		lv_label_set_text(gui->label_info, "#FFDD00 初始化eMMC失败!#");
		goto out;
	}

	int i = 0;
	char sdPath[OUT_FILENAME_SZ];
	// Create Restore folders, if they do not exist.
	emmcsn_path_impl(sdPath, "/restore", "", &emmc_storage);
	emmcsn_path_impl(sdPath, "/restore/emummc", "", &emmc_storage);
	emmcsn_path_impl(sdPath, "/restore/partitions", "", &emmc_storage);

	// Set folder to backup/{emmc_sn}.
	emmcsn_path_impl(sdPath, "", "", &emmc_storage);
	gui->base_path = (char *)malloc(strlen(sdPath) + 1);
	strcpy(gui->base_path, sdPath);

	timer = get_tmr_s();
	if (dumpType & PART_BOOT)
	{
		const u32 BOOT_PART_SIZE = emmc_storage.ext_csd.boot_mult << 17;
		const u32 BOOT_PART_SECTORS = 0x2000; // Force 4 MiB for emuMMC.

		emmc_part_t bootPart;
		memset(&bootPart, 0, sizeof(bootPart));
		bootPart.lba_start = 0;
		if (!gui->raw_emummc)
			bootPart.lba_end = (BOOT_PART_SIZE / EMMC_BLOCKSIZE) - 1;
		else
			bootPart.lba_end = BOOT_PART_SECTORS - 1;
		for (i = 0; i < 2; i++)
		{
			strcpy(bootPart.name, "BOOT");
			bootPart.name[4] = (u8)('0' + i);
			bootPart.name[5] = 0;

			s_printf(txt_buf, "#00DDFF %02d: %s#\n#00DDFF 范围: 0x%08X - 0x%08X#\n\n",
				i, bootPart.name, bootPart.lba_start, bootPart.lba_end);
			lv_label_set_text(gui->label_info, txt_buf);
			s_printf(txt_buf, "%02d: %s... ", i, bootPart.name);
			lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, txt_buf);
			manual_system_maintenance(true);

			emmc_set_partition(i + 1);

			// Set filename to backup/{emmc_sn}/BOOT0/1 or backup/{emmc_sn}/emummc/BOOT0/1.
			if (!gui->raw_emummc)
				emmcsn_path_impl(sdPath, "",        bootPart.name, &emmc_storage);
			else
				emmcsn_path_impl(sdPath, "/emummc", bootPart.name, &emmc_storage);

			res = _dump_emmc_part(gui, sdPath, i, &emmc_storage, &bootPart);

			if (res)
				strcpy(txt_buf, "#FFDD00 失败!#\n");
			else
				strcpy(txt_buf, "完成!\n");

			lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, txt_buf);
			manual_system_maintenance(true);
		}
	}

	if ((dumpType & PART_SYSTEM) || (dumpType & PART_USER) || (dumpType & PART_RAW))
	{
		emmc_set_partition(EMMC_GPP);

		if ((dumpType & PART_SYSTEM) || (dumpType & PART_USER))
		{
			emmcsn_path_impl(sdPath, "/partitions", "", &emmc_storage);
			gui->base_path = (char *)malloc(strlen(sdPath) + 1);
			strcpy(gui->base_path, sdPath);

			LIST_INIT(gpt);
			emmc_gpt_parse(&gpt);
			LIST_FOREACH_ENTRY(emmc_part_t, part, &gpt, link)
			{
				if ((dumpType & PART_USER) == 0 && !strcmp(part->name, "USER"))
					continue;
				if ((dumpType & PART_SYSTEM) == 0 && strcmp(part->name, "USER"))
					continue;

				s_printf(txt_buf, "#00DDFF %02d: %s#\n#00DDFF 范围: 0x%08X - 0x%08X#\n\n",
					i, part->name, part->lba_start, part->lba_end);
				lv_label_set_text(gui->label_info, txt_buf);
				s_printf(txt_buf, "%02d: %s... ", i, part->name);
				lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, txt_buf);
				manual_system_maintenance(true);
				i++;

				emmcsn_path_impl(sdPath, "/partitions", part->name, &emmc_storage);
				res = _dump_emmc_part(gui, sdPath, 0, &emmc_storage, part);
				// If a part failed, don't continue.
				if (res)
				{
					strcpy(txt_buf, "#FFDD00 失败!#\n");
					lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, txt_buf);
					break;
				}
				else
					strcpy(txt_buf, "完成!\n");

				lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, txt_buf);
				manual_system_maintenance(true);
			}
			emmc_gpt_free(&gpt);
		}

		if (dumpType & PART_RAW)
		{
			// Get GP partition size dynamically.
			const u32 RAW_AREA_NUM_SECTORS = emmc_storage.sec_cnt;

			emmc_part_t rawPart;
			memset(&rawPart, 0, sizeof(rawPart));
			rawPart.lba_start = 0;
			rawPart.lba_end = RAW_AREA_NUM_SECTORS - 1;
			strcpy(rawPart.name, "rawnand.bin");
			{
				s_printf(txt_buf, "#00DDFF %02d: %s#\n#00DDFF 范围: 0x%08X - 0x%08X#\n\n",
					i, rawPart.name, rawPart.lba_start, rawPart.lba_end);
				lv_label_set_text(gui->label_info, txt_buf);
				s_printf(txt_buf, "%02d: %s... ", i, rawPart.name);
				lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, txt_buf);
				manual_system_maintenance(true);

				i++;

				// Set filename to backup/{emmc_sn}/rawnand.bin or backup/{emmc_sn}/emummc/rawnand.bin.
				if (!gui->raw_emummc)
					emmcsn_path_impl(sdPath, "",        rawPart.name, &emmc_storage);
				else
					emmcsn_path_impl(sdPath, "/emummc", rawPart.name, &emmc_storage);

				res = _dump_emmc_part(gui, sdPath, 2, &emmc_storage, &rawPart);

				if (res)
					strcpy(txt_buf, "#FFDD00 失败!#\n");
				else
					strcpy(txt_buf, "完成!\n");

				lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, txt_buf);
				manual_system_maintenance(true);
			}
		}
	}

	timer = get_tmr_s() - timer;
	emmc_end();

	if (!res && n_cfg.verification && !gui->raw_emummc)
		s_printf(txt_buf, "耗时: %d分%d秒.\n#96FF00 已完成并验证通过!#", timer / 60, timer % 60);
	else if (!res)
		s_printf(txt_buf, "耗时: %d分%d秒.\n完成!", timer / 60, timer % 60);
	else
		s_printf(txt_buf, "耗时: %d分%d秒.", timer / 60, timer % 60);

	lv_label_set_text(gui->label_finish, txt_buf);

out:
	free(txt_buf);
	free(gui->base_path);
	if (!partial_sd_full_unmount)
		sd_unmount();
	else
	{
		partial_sd_full_unmount = false;
		sd_end();
	}
}

static int _restore_emmc_part(emmc_tool_gui_t *gui, char *sd_path, int active_part, sdmmc_storage_t *storage, emmc_part_t *part, bool allow_multi_part)
{
	static const u32 SECTORS_TO_MIB_COEFF = 11;

	u32 verification = n_cfg.verification;
	u32 lba_end = part->lba_end;
	u32 totalSectors = part->lba_end - part->lba_start + 1;
	u32 currPartIdx = 0;
	u32 numSplitParts = 0;
	u32 lbaStartPart = part->lba_start;
	int res = 0;
	char *outFilename = sd_path;
	u32 sdPathLen = strlen(sd_path);
	u64 fileSize = 0;
	u64 totalCheckFileSize = 0;

	FIL fp;
	FILINFO fno;

	lv_bar_set_value(gui->bar, 0);
	lv_label_set_text(gui->label_pct, " "SYMBOL_DOT" 0%");
	lv_bar_set_style(gui->bar, LV_BAR_STYLE_BG, gui->bar_orange_bg);
	lv_bar_set_style(gui->bar, LV_BAR_STYLE_INDIC, gui->bar_orange_ind);
	manual_system_maintenance(true);

	bool use_multipart = false;
	bool check_4MB_aligned = true;

	if (!allow_multi_part)
		goto multipart_not_allowed;

	// Check to see if there is a combined file and if so then use that.
	if (f_stat(outFilename, &fno))
	{
		// If not, check if there are partial files and the total size matches.
		strcpy(gui->txt_buf, "\n没有单个文件, 正在检查部分文件...\n");
		lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
		manual_system_maintenance(true);

		outFilename[sdPathLen++] = '.';

		_update_filename(outFilename, sdPathLen, numSplitParts);

		s_printf(gui->txt_buf, "#96FF00 文件路径:#\n%s\n#96FF00 文件名:# #FF8000 %s#",
			gui->base_path, outFilename + strlen(gui->base_path));
		lv_label_ins_text(gui->label_info, LV_LABEL_POS_LAST, gui->txt_buf);

		// Stat total size of the part files.
		while ((u32)((u64)totalCheckFileSize >> (u64)9) != totalSectors)
		{
			_update_filename(outFilename, sdPathLen, numSplitParts);

			s_printf(gui->txt_buf, "%s#", outFilename + strlen(gui->base_path));
			lv_label_cut_text(gui->label_info,
				lv_txt_get_encoded_length(lv_label_get_text(gui->label_info)) - strlen(outFilename + strlen(gui->base_path)) - 1,
				strlen(outFilename + strlen(gui->base_path)) + 1);
			lv_label_ins_text(gui->label_info, LV_LABEL_POS_LAST, gui->txt_buf);
			manual_system_maintenance(true);

			if ((u32)((u64)totalCheckFileSize >> (u64)9) > totalSectors)
			{
				strcpy(gui->txt_buf, "\n#FF8000 SD卡分卷备份大小超过所选#\n#FF8000 eMMC分区大小!#\n#FFDD00 操作已中止...#");
				lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
				manual_system_maintenance(true);

				return 1;
			}
			else if (f_stat(outFilename, &fno))
			{
				if (!gui->raw_emummc)
				{
					s_printf(gui->txt_buf, "\n#FFDD00 错误: 未找到文件#\n#FFDD00 %s.#\n\n", outFilename);
					lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
					manual_system_maintenance(true);

					// Attempt a smaller restore.
					if (numSplitParts)
						break;
				}
				else
				{
					// Set new total sectors and lba end sector for percentage calculations.
					totalSectors = (u32)((u64)totalCheckFileSize >> (u64)9);
					part->lba_end = totalSectors + part->lba_start - 1;
					lba_end = part->lba_end;
				}

				// Restore folder is empty.
				if (!numSplitParts)
				{
					strcpy(gui->txt_buf, "\n#FFDD00 恢复文件夹为空.#\n\n");
					lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
					manual_system_maintenance(true);

					return 1;
				}
			}
			else
			{
				totalCheckFileSize += (u64)fno.fsize;

				if (check_4MB_aligned && (((u64)fno.fsize) % SZ_4M))
				{
					strcpy(gui->txt_buf, "\n#FFDD00 分卷文件大小必须是#\n#FFDD00 4 MiB的整数倍.#\n#FFDD00 正在中止...#");
					lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
					manual_system_maintenance(true);

					return 1;
				}

				check_4MB_aligned = false;
			}

			numSplitParts++;
		}

		s_printf(gui->txt_buf, "共计%X个扇区.\n", (u32)((u64)totalCheckFileSize >> (u64)9));
		lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
		manual_system_maintenance(true);

		if ((u32)((u64)totalCheckFileSize >> (u64)9) != totalSectors)
		{
			lv_obj_t *warn_mbox_bg = create_mbox_text(
				"#FF8000 SD卡分卷备份文件大小与#\n#FF8000 所选的eMMC部分大小不匹配!#\n\n"
				"#FFDD00 备份文件可能已损坏#\n#FFDD00 或缺少文件!#\n#FFDD00 建议中止本次操作!#\n\n"
				"按 #FF8000 电源键# 继续.\n按 #FF8000 音量键# 中止.", false);
			manual_system_maintenance(true);

			if (!(btn_wait() & BTN_POWER))
			{
				lv_obj_del(warn_mbox_bg);
				strcpy(gui->txt_buf, "\n#FF0000 SD卡分卷文件大小与#\n#FF0000 所选的eMMC部分大小不匹配!#\n");
				lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
				manual_system_maintenance(true);

				return 1;
			}
			lv_obj_del(warn_mbox_bg);

			// Set new total sectors and lba end sector for percentage calculations.
			totalSectors = (u32)((u64)totalCheckFileSize >> (u64)9);
			part->lba_end = totalSectors + part->lba_start - 1;
			lba_end = part->lba_end;
		}
		use_multipart = true;
		_update_filename(outFilename, sdPathLen, 0);
	}

multipart_not_allowed:
	res = f_open(&fp, outFilename, FA_READ);
	if (use_multipart)
	{
		s_printf(gui->txt_buf, "%s#", outFilename + strlen(gui->base_path));
		lv_label_cut_text(gui->label_info,
			lv_txt_get_encoded_length(lv_label_get_text(gui->label_info)) - strlen(outFilename + strlen(gui->base_path)) - 1,
			strlen(outFilename + strlen(gui->base_path)) + 1);
		lv_label_ins_text(gui->label_info, LV_LABEL_POS_LAST, gui->txt_buf);
		manual_system_maintenance(true);
	}
	else
	{
		s_printf(gui->txt_buf, "#96FF00 文件路径:#\n%s\n#96FF00 文件名:# #FF8000 %s#",
			gui->base_path, outFilename + strlen(gui->base_path));
			lv_label_ins_text(gui->label_info, LV_LABEL_POS_LAST, gui->txt_buf);
	}
	manual_system_maintenance(true);
	if (res)
	{
		if (res != FR_NO_FILE)
		{
			s_printf(gui->txt_buf, "\n#FF0000 错误 (%d) 打开文件失败. 继续...#\n", res);
			lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
			manual_system_maintenance(true);
		}
		else
		{
			s_printf(gui->txt_buf, "\n#FFDD00 错误 (%d) 未找到文件. 继续...#\n", res);
			lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
			manual_system_maintenance(true);
		}

		return 2;
	}
	else if (!use_multipart && (((u32)((u64)f_size(&fp) >> (u64)9)) != totalSectors)) // Check total restore size vs emmc size.
	{
		if (((u32)((u64)f_size(&fp) >> (u64)9)) > totalSectors)
		{
			strcpy(gui->txt_buf, "\n#FF8000 SD卡备份大小超过了#\n#FF8000 所选的eMMC部分大小!#\n#FFDD00 正在中止...#");
			lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
			manual_system_maintenance(true);

			f_close(&fp);

			return 1;
		}
		else if (!gui->raw_emummc)
		{
			lv_obj_t *warn_mbox_bg = create_mbox_text(
				"#FF8000 SD卡备份文件大小与#\n#FF8000 所选的eMMC部分大小不匹配!#\n\n"
				"#FFDD00 备份文件可能已损坏!#\n#FFDD00 建议中止本次操作!#\n\n"
				"按 #FF8000 电源键# 继续.\n按 #FF8000 音量键# 中止.", false);
			manual_system_maintenance(true);

			if (!(btn_wait() & BTN_POWER))
			{
				lv_obj_del(warn_mbox_bg);
				strcpy(gui->txt_buf, "\n#FF0000 SD卡备份文件大小与#\n#FF0000 所选的eMMC部分大小不匹配.#\n");
				lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
				manual_system_maintenance(true);

				f_close(&fp);

				return 1;
			}
			lv_obj_del(warn_mbox_bg);
		}
		// Set new total sectors and lba end sector for percentage calculations.
		totalSectors = (u32)((u64)f_size(&fp) >> (u64)9);
		lba_end = totalSectors + part->lba_start - 1;
	}
	else
	{
		fileSize = (u64)f_size(&fp);
		s_printf(gui->txt_buf, "\n总恢复文件大小: %d MiB.\n",
			(u32)((use_multipart ? (u64)totalCheckFileSize : fileSize) >> (u64)9) >> SECTORS_TO_MIB_COEFF);
		lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
		manual_system_maintenance(true);
	}

	u8 *buf = (u8 *)MIXD_BUF_ALIGNED;

	u32 lba_curr = part->lba_start;
	u32 bytesWritten = 0;
	u32 prevPct = 200;
	int retryCount = 0;

	u32 num = 0;
	u32 pct = 0;

	DWORD *clmt = f_expand_cltbl(&fp, SZ_4M, 0);

	u32 sector_start = 0, part_idx = 0;
	u32 sector_size = totalSectors;
	u32 sd_sector_off = 0;

	if (gui->raw_emummc)
	{
		_get_valid_partition(&sector_start, &sector_size, &part_idx, false);
		if (!part_idx || !sector_size)
		{
			strcpy(gui->txt_buf, "\n#FFDD00 未找到分区...#\n");
			lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
			manual_system_maintenance(true);

			return 1;
		}
		sd_sector_off = sector_start + (0x2000 * active_part);
	}

	lv_obj_set_opa_scale(gui->bar, LV_OPA_COVER);
	lv_obj_set_opa_scale(gui->label_pct, LV_OPA_COVER);
	while (totalSectors > 0)
	{
		// If we have more than one part, check the size for the split parts and make sure that the bytes written is not more than that.
		if (numSplitParts != 0 && bytesWritten >= fileSize)
		{
			// If we have more bytes written then close the file pointer and increase the part index we are using
			f_close(&fp);
			free(clmt);
			memset(&fp, 0, sizeof(fp));
			currPartIdx++;

			if (verification && !gui->raw_emummc)
			{
				// Verify part.
				res = _emmc_sd_copy_verify(gui, storage, lbaStartPart, outFilename, part);
				switch (res)
				{
				case VERIF_STATUS_OK:
					break;
				case VERIF_STATUS_ERROR:
					strcpy(gui->txt_buf, "\n#FFDD00 请重试...#\n");
					lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
					manual_system_maintenance(true);
					return 1;
				case VERIF_STATUS_ABORT:
					verification = 0;
					break;
				}
				lv_bar_set_style(gui->bar, LV_BAR_STYLE_BG, gui->bar_orange_bg);
				lv_bar_set_style(gui->bar, LV_BAR_STYLE_INDIC, gui->bar_orange_ind);
			}

			_update_filename(outFilename, sdPathLen, currPartIdx);

			// Read from next part.
			s_printf(gui->txt_buf, "%s#", outFilename + strlen(gui->base_path));
			lv_label_cut_text(gui->label_info,
				lv_txt_get_encoded_length(lv_label_get_text(gui->label_info)) - strlen(outFilename + strlen(gui->base_path)) - 1,
				strlen(outFilename + strlen(gui->base_path)) + 1);
			lv_label_ins_text(gui->label_info, LV_LABEL_POS_LAST, gui->txt_buf);
			manual_system_maintenance(true);

			lbaStartPart = lba_curr;

			// Try to open the next file part
			res = f_open(&fp, outFilename, FA_READ);
			if (res)
			{
				s_printf(gui->txt_buf, "\n#FF0000 打开文件时出错 (%d)#\n#FFDD00 %s!#\n", res, outFilename);
				lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
				manual_system_maintenance(true);

				return 1;
			}
			fileSize = (u64)f_size(&fp);
			bytesWritten = 0;
			clmt = f_expand_cltbl(&fp, SZ_4M, 0);
		}

		retryCount = 0;
		num = MIN(totalSectors, NUM_SECTORS_PER_ITER);

		res = f_read_fast(&fp, buf, num << 9);
		manual_system_maintenance(false);

		if (res)
		{
			s_printf(gui->txt_buf,
				"\n#FF0000 读取SD卡时发生严重错误 (%d)!#\n"
				"#FF0000 此设备可能处于非工作状态!#\n"
				"#FFDD00 请立刻重试!#\n", res);
			lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
			manual_system_maintenance(true);

			f_close(&fp);
			free(clmt);
			return 1;
		}
		if (!gui->raw_emummc)
			res = sdmmc_storage_write(storage, lba_curr, num, buf);
		else
			res = sdmmc_storage_write(&sd_storage, lba_curr + sd_sector_off, num, buf);

		manual_system_maintenance(false);

		while (res)
		{
			s_printf(gui->txt_buf,
				"\n#FFDD00 向eMMC写入%d个块时出错 @ LBA %08X#\n"
				"#FFDD00 第%d次重试. #",
				num, lba_curr, ++retryCount);
			lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
			manual_system_maintenance(true);

			msleep(150);
			if (retryCount >= 3)
			{
				strcpy(gui->txt_buf, "#FF0000 正在中止...#\n"
					"#FF0000 这个设备可能处于无法操作的状态!#\n"
					"#FFDD00 请立刻重试!#\n");
				lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
				manual_system_maintenance(true);

				f_close(&fp);
				free(clmt);
				return 1;
			}
			else
			{
				strcpy(gui->txt_buf, "#FFDD00 重试中...#\n");
				lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
				manual_system_maintenance(true);
			}
			if (!gui->raw_emummc)
				res = sdmmc_storage_write(storage, lba_curr, num, buf);
			else
				res = sdmmc_storage_write(&sd_storage, lba_curr + sd_sector_off, num, buf);
			manual_system_maintenance(false);
		}
		pct = (u64)((u64)(lba_curr - part->lba_start) * 100u) / (u64)(lba_end - part->lba_start);
		if (pct != prevPct)
		{
			lv_bar_set_value(gui->bar, pct);
			s_printf(gui->txt_buf, " "SYMBOL_DOT" %d%%", pct);
			lv_label_set_text(gui->label_pct, gui->txt_buf);
			manual_system_maintenance(true);
			prevPct = pct;
		}

		lba_curr += num;
		totalSectors -= num;
		bytesWritten += num * EMMC_BLOCKSIZE;
	}
	lv_bar_set_value(gui->bar, 100);
	lv_label_set_text(gui->label_pct, " "SYMBOL_DOT" 100%");
	manual_system_maintenance(true);

	// Restore operation ended successfully.
	f_close(&fp);
	free(clmt);

	if (verification && !gui->raw_emummc)
	{
		// Verify restored data.
		if (_emmc_sd_copy_verify(gui, storage, lbaStartPart, outFilename, part) == VERIF_STATUS_ERROR)
		{
			strcpy(gui->txt_buf, "\n#FFDD00 请重试...#\n");
			lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, gui->txt_buf);
			manual_system_maintenance(true);

			return 1;
		}
		lv_bar_set_value(gui->bar, 100);
		lv_label_set_text(gui->label_pct, " "SYMBOL_DOT" 100%");
		manual_system_maintenance(true);
	}

	if (gui->raw_emummc)
	{
		char sdPath[OUT_FILENAME_SZ];
		// Create Restore folders, if they do not exist.
		f_mkdir("emuMMC");
		s_printf(sdPath, "emuMMC/RAW%d", part_idx);
		f_mkdir(sdPath);
		strcat(sdPath, "/raw_based");
		FIL fp_raw;
		f_open(&fp_raw, sdPath, FA_CREATE_ALWAYS | FA_WRITE);
		f_write(&fp_raw, &sector_start, 4, NULL);
		f_close(&fp_raw);

		s_printf(sdPath, "emuMMC/RAW%d", part_idx);
		save_emummc_cfg(part_idx, sector_start, sdPath);
	}

	return 0;
}

void restore_emmc_selected(emmcPartType_t restoreType, emmc_tool_gui_t *gui)
{
	int res = 0;
	u32 timer = 0;

	char *txt_buf = (char *)malloc(SZ_16K);
	gui->txt_buf = txt_buf;

	txt_buf[0] = 0;
	lv_label_set_text(gui->label_log, txt_buf);

	manual_system_maintenance(true);

	if (!gui->raw_emummc)
		strcpy(txt_buf, "#FFDD00 可能会导致设备无法正常工作!#");
	else
		strcpy(txt_buf, "#FFDD00 可能会导致emuMMC无法正常工作!#");
	strcat(txt_buf, "\n\n#FFDD00 你确定要继续吗?#");

	if (gui->raw_emummc)
		strcat(txt_buf, "\n\n只能恢复检测到的第一个emuMMC!");
	if ((restoreType & PART_BOOT) || (restoreType & PART_GP_ALL))
	{
		strcat(txt_buf,
			"\n\n您选择的模式\n只会恢复检测到的分区.\n"
			"未检测到的分区会被跳过, \n并继续处理下一个分区.");
	}

	u32 orig_msg_len = strlen(txt_buf);

	lv_obj_t *warn_mbox_bg = create_mbox_text(txt_buf, false);
	lv_obj_t *warn_mbox = lv_obj_get_child(warn_mbox_bg, NULL);

	u8 failsafe_wait = 6;
	while (failsafe_wait > 0)
	{
		s_printf(txt_buf + orig_msg_len, "\n\n#888888 等待... (%d秒)#", failsafe_wait);
		lv_mbox_set_text(warn_mbox, txt_buf);
		msleep(1000);
		manual_system_maintenance(true);
		failsafe_wait--;
	}

	s_printf(txt_buf + orig_msg_len, "\n\n按 #FF8000 电源键# 继续.\n按 #FF8000 音量键# 中断.");
	lv_mbox_set_text(warn_mbox, txt_buf);
	manual_system_maintenance(true);

	if (!(btn_wait() & BTN_POWER))
	{
		lv_label_set_text(gui->label_info, "#FFDD00 恢复操作已中止!#");
		lv_obj_del(warn_mbox_bg);
		goto out;
	}
	lv_obj_del(warn_mbox_bg);
	manual_system_maintenance(true);

	if (sd_mount())
	{
		lv_label_set_text(gui->label_info, "#FFDD00 初始化SD卡失败!#");
		goto out;
	}

	if (emmc_initialize(false))
	{
		lv_label_set_text(gui->label_info, "#FFDD00 初始化eMMC失败!#");
		goto out;
	}

	int i = 0;
	char sdPath[OUT_FILENAME_SZ];
	if (!gui->raw_emummc)
		emmcsn_path_impl(sdPath, "/restore", "", &emmc_storage);
	else
		emmcsn_path_impl(sdPath, "/restore/emummc", "", &emmc_storage);
	gui->base_path = (char *)malloc(strlen(sdPath) + 1);
	strcpy(gui->base_path, sdPath);

	timer = get_tmr_s();
	if (restoreType & PART_BOOT)
	{
		const u32 BOOT_PART_SIZE = emmc_storage.ext_csd.boot_mult << 17;
		const u32 BOOT_PART_SECTORS = 0x2000; // Force 4 MiB for emuMMC.

		emmc_part_t bootPart;
		memset(&bootPart, 0, sizeof(bootPart));
		bootPart.lba_start = 0;
		if (!gui->raw_emummc)
			bootPart.lba_end = (BOOT_PART_SIZE / EMMC_BLOCKSIZE) - 1;
		else
			bootPart.lba_end = BOOT_PART_SECTORS - 1;
		for (i = 0; i < 2; i++)
		{
			strcpy(bootPart.name, "BOOT");
			bootPart.name[4] = (u8)('0' + i);
			bootPart.name[5] = 0;

			s_printf(txt_buf, "#00DDFF %02d: %s#\n#00DDFF 范围: 0x%08X - 0x%08X#\n\n\n\n\n",
				i, bootPart.name, bootPart.lba_start, bootPart.lba_end);
			lv_label_set_text(gui->label_info, txt_buf);
			s_printf(txt_buf, "%02d: %s... ", i, bootPart.name);
			lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, txt_buf);
			manual_system_maintenance(true);

			emmc_set_partition(i + 1);

			if (!gui->raw_emummc)
				emmcsn_path_impl(sdPath, "/restore", bootPart.name, &emmc_storage);
			else
				emmcsn_path_impl(sdPath, "/restore/emummc", bootPart.name, &emmc_storage);
			res = _restore_emmc_part(gui, sdPath, i, &emmc_storage, &bootPart, false);

			if (res == 1)
				strcpy(txt_buf, "#FFDD00 失败!#\n");
			else if (!res)
				strcpy(txt_buf, "完成!\n");

			if (res <= 1)
				lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, txt_buf);

			manual_system_maintenance(true);
		}
	}

	if (restoreType & PART_GP_ALL)
	{
		emmcsn_path_impl(sdPath, "/restore/partitions", "", &emmc_storage);
		gui->base_path = (char *)malloc(strlen(sdPath) + 1);
		strcpy(gui->base_path, sdPath);

		emmc_set_partition(EMMC_GPP);

		LIST_INIT(gpt);
		emmc_gpt_parse(&gpt);
		LIST_FOREACH_ENTRY(emmc_part_t, part, &gpt, link)
		{
			s_printf(txt_buf, "#00DDFF %02d: %s#\n#00DDFF 范围: 0x%08X - 0x%08X#\n\n\n\n\n",
				i, part->name, part->lba_start, part->lba_end);
			lv_label_set_text(gui->label_info, txt_buf);
			s_printf(txt_buf, "%02d: %s... ", i, part->name);
			lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, txt_buf);
			manual_system_maintenance(true);
			i++;

			emmcsn_path_impl(sdPath, "/restore/partitions", part->name, &emmc_storage);
			res = _restore_emmc_part(gui, sdPath, 0, &emmc_storage, part, false);

			if (res == 1)
				strcpy(txt_buf, "#FFDD00 失败!#\n");
			else if (!res)
				strcpy(txt_buf, "完成!\n");

			if (res <= 1)
				lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, txt_buf);

			manual_system_maintenance(true);
		}
		emmc_gpt_free(&gpt);
	}

	if (restoreType & PART_RAW)
	{
		// Get GP partition size dynamically.
		const u32 RAW_AREA_NUM_SECTORS = emmc_storage.sec_cnt;

		emmc_part_t rawPart;
		memset(&rawPart, 0, sizeof(rawPart));
		rawPart.lba_start = 0;
		rawPart.lba_end = RAW_AREA_NUM_SECTORS - 1;
		strcpy(rawPart.name, "rawnand.bin");
		{
			s_printf(txt_buf, "#00DDFF %02d: %s#\n#00DDFF 范围: 0x%08X - 0x%08X#\n\n\n\n\n",
				i, rawPart.name, rawPart.lba_start, rawPart.lba_end);
			lv_label_set_text(gui->label_info, txt_buf);
			s_printf(txt_buf, "%02d: %s... ", i, rawPart.name);
			lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, txt_buf);
			manual_system_maintenance(true);
			i++;

			if (!gui->raw_emummc)
				emmcsn_path_impl(sdPath, "/restore", rawPart.name, &emmc_storage);
			else
				emmcsn_path_impl(sdPath, "/restore/emummc", rawPart.name, &emmc_storage);
			res = _restore_emmc_part(gui, sdPath, 2, &emmc_storage, &rawPart, true);

			if (res == 1)
				strcpy(txt_buf, "#FFDD00 失败!#\n");
			else if (!res)
				strcpy(txt_buf, "完成!\n");

			if (res <= 1)
				lv_label_ins_text(gui->label_log, LV_LABEL_POS_LAST, txt_buf);

			manual_system_maintenance(true);
		}
	}

	timer = get_tmr_s() - timer;
	emmc_end();

	if (!res && n_cfg.verification && !gui->raw_emummc)
		s_printf(txt_buf, "耗时: %d分%d秒.\n#96FF00 完成并通过校验!#", timer / 60, timer % 60);
	else if (!res)
		s_printf(txt_buf, "耗时: %d分%d秒.\n完成!", timer / 60, timer % 60);
	else
		s_printf(txt_buf, "耗时: %d分%d秒.", timer / 60, timer % 60);

	lv_label_set_text(gui->label_finish, txt_buf);

out:
	free(txt_buf);
	free(gui->base_path);
	sd_unmount();
}
