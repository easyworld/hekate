/*
 * Copyright (c) 2018 naehrwert
 * Copyright (c) 2018-2024 CTCaer
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

#include <stdlib.h>

#include <bdk.h>

#include "gui.h"
#include "gui_tools.h"
#include "gui_tools_partition_manager.h"
#include "gui_emmc_tools.h"
#include "fe_emummc_tools.h"
#include "../config.h"
#include "../hos/pkg1.h"
#include "../hos/pkg2.h"
#include "../hos/hos.h"
#include <libs/fatfs/ff.h>

extern volatile boot_cfg_t *b_cfg;
extern hekate_config h_cfg;
extern nyx_config n_cfg;

lv_obj_t *ums_mbox;

extern char *emmcsn_path_impl(char *path, char *sub_dir, char *filename, sdmmc_storage_t *storage);

static lv_obj_t *_create_container(lv_obj_t *parent)
{
	static lv_style_t h_style;
	lv_style_copy(&h_style, &lv_style_transp);
	h_style.body.padding.inner = 0;
	h_style.body.padding.hor = LV_DPI - (LV_DPI / 4);
	h_style.body.padding.ver = LV_DPI / 6;

	lv_obj_t *h1 = lv_cont_create(parent, NULL);
	lv_cont_set_style(h1, &h_style);
	lv_cont_set_fit(h1, false, true);
	lv_obj_set_width(h1, (LV_HOR_RES / 9) * 4);
	lv_obj_set_click(h1, false);
	lv_cont_set_layout(h1, LV_LAYOUT_OFF);

	return h1;
}

bool get_set_autorcm_status(bool toggle)
{
	u32 sector;
	u8 corr_mod0, mod1;
	bool enabled = false;

	if (h_cfg.t210b01)
		return false;

	emmc_initialize(false);

	u8 *tempbuf = (u8 *)malloc(0x200);
	emmc_set_partition(EMMC_BOOT0);
	sdmmc_storage_read(&emmc_storage, 0x200 / EMMC_BLOCKSIZE, 1, tempbuf);

	// Get the correct RSA modulus byte masks.
	nx_emmc_get_autorcm_masks(&corr_mod0, &mod1);

	// Check if 2nd byte of modulus is correct.
	if (tempbuf[0x11] != mod1)
		goto out;

	if (tempbuf[0x10] != corr_mod0)
		enabled = true;

	// Toggle autorcm status if requested.
	if (toggle)
	{
		// Iterate BCTs.
		for (u32 i = 0; i < 4; i++)
		{
			sector = (0x200 + (0x4000 * i)) / EMMC_BLOCKSIZE; // 0x4000 bct + 0x200 offset.
			sdmmc_storage_read(&emmc_storage, sector, 1, tempbuf);

			if (!enabled)
				tempbuf[0x10] = 0;
			else
				tempbuf[0x10] = corr_mod0;
			sdmmc_storage_write(&emmc_storage, sector, 1, tempbuf);
		}
		enabled = !enabled;
	}

	// Check if RCM is patched and protect from a possible brick.
	if (enabled && h_cfg.rcm_patched && hw_get_chip_id() != GP_HIDREV_MAJOR_T210B01)
	{
		// Iterate BCTs.
		for (u32 i = 0; i < 4; i++)
		{
			sector = (0x200 + (0x4000 * i)) / EMMC_BLOCKSIZE; // 0x4000 bct + 0x200 offset.
			sdmmc_storage_read(&emmc_storage, sector, 1, tempbuf);

			// Check if 2nd byte of modulus is correct.
			if (tempbuf[0x11] != mod1)
				continue;

			// If AutoRCM is enabled, disable it.
			if (tempbuf[0x10] != corr_mod0)
			{
				tempbuf[0x10] = corr_mod0;

				sdmmc_storage_write(&emmc_storage, sector, 1, tempbuf);
			}
		}

		enabled = false;
	}

out:
	free(tempbuf);
	emmc_end();

	h_cfg.autorcm_enabled = enabled;

	return enabled;
}

static lv_res_t _create_mbox_autorcm_status(lv_obj_t *btn)
{
	lv_obj_t *dark_bg = lv_obj_create(lv_scr_act(), NULL);
	lv_obj_set_style(dark_bg, &mbox_darken);
	lv_obj_set_size(dark_bg, LV_HOR_RES, LV_VER_RES);

	static const char * mbox_btn_map[] = { "\251", "\222確定", "\251", "" };
	lv_obj_t * mbox = lv_mbox_create(dark_bg, NULL);
	lv_mbox_set_recolor_text(mbox, true);

	bool enabled = get_set_autorcm_status(true);

	if (enabled)
	{
		lv_mbox_set_text(mbox,
			"AutoRCM現在已經 #C7EA46 開啟!#\n\n"
			"您現在只需按下 #FF8000 電源鍵# 即可自動進入RCM模式.\n"
			"如果想要在以後取消AutoRCM, 請再次使用此處的AutoRCM按鈕.");
	}
	else
	{
		lv_mbox_set_text(mbox,
			"AutoRCM現在已經#FF8000 關閉!#\n\n"
			"現在啟動過程已恢復正常, 您需要使用 #FF8000 音量+# 和 #FF8000 HOME# (使用短接器) 組合鍵才能進入RCM模式.\n");
	}

	lv_mbox_add_btns(mbox, mbox_btn_map, mbox_action);
	lv_obj_set_width(mbox, LV_HOR_RES / 9 * 5);
	lv_obj_align(mbox, NULL, LV_ALIGN_CENTER, 0, 0);
	lv_obj_set_top(mbox, true);

	if (enabled)
		lv_btn_set_state(btn, LV_BTN_STATE_TGL_REL);
	else
		lv_btn_set_state(btn, LV_BTN_STATE_REL);
	nyx_generic_onoff_toggle(btn);

	return LV_RES_OK;
}

static lv_res_t _create_mbox_hid(usb_ctxt_t *usbs)
{
	lv_obj_t *dark_bg = lv_obj_create(lv_scr_act(), NULL);
	lv_obj_set_style(dark_bg, &mbox_darken);
	lv_obj_set_size(dark_bg, LV_HOR_RES, LV_VER_RES);

	static const char *mbox_btn_map[] = { "\251", "\262關閉", "\251", "" };
	static const char *mbox_btn_map2[] = { "\251", "\222關閉", "\251", "" };
	lv_obj_t *mbox = lv_mbox_create(dark_bg, NULL);
	lv_mbox_set_recolor_text(mbox, true);

	char *txt_buf = malloc(SZ_4K);

	s_printf(txt_buf, "#FF8000 HID模擬#\n\n#C7EA46 裝置:# ");

	if (usbs->type == USB_HID_GAMEPAD)
		strcat(txt_buf, "手柄");
	else
		strcat(txt_buf, "觸控板");

	lv_mbox_set_text(mbox, txt_buf);
	free(txt_buf);

	lv_obj_t *lbl_status = lv_label_create(mbox, NULL);
	lv_label_set_recolor(lbl_status, true);
	lv_label_set_text(lbl_status, " ");
	usbs->label = (void *)lbl_status;

	lv_obj_t *lbl_tip = lv_label_create(mbox, NULL);
	lv_label_set_recolor(lbl_tip, true);
	lv_label_set_static_text(lbl_tip, "提示: 如果想要結束, 可以按 #C7EA46 L3# + #C7EA46 HOME# 或者斷開連線線.");
	lv_obj_set_style(lbl_tip, &hint_small_style);

	lv_mbox_add_btns(mbox, mbox_btn_map, mbox_action);
	lv_obj_set_width(mbox, LV_HOR_RES / 9 * 5);
	lv_obj_align(mbox, NULL, LV_ALIGN_CENTER, 0, 0);
	lv_obj_set_top(mbox, true);

	usb_device_gadget_hid(usbs);

	lv_mbox_add_btns(mbox, mbox_btn_map2, mbox_action);

	return LV_RES_OK;
}

static lv_res_t _create_mbox_ums(usb_ctxt_t *usbs)
{
	lv_obj_t *dark_bg = lv_obj_create(lv_scr_act(), NULL);
	lv_obj_set_style(dark_bg, &mbox_darken);
	lv_obj_set_size(dark_bg, LV_HOR_RES, LV_VER_RES);

	static const char *mbox_btn_map[] = { "\251", "\262關閉", "\251", "" };
	static const char *mbox_btn_map2[] = { "\251", "\222關閉", "\251", "" };
	lv_obj_t *mbox = lv_mbox_create(dark_bg, NULL);
	lv_mbox_set_recolor_text(mbox, true);

	char *txt_buf = malloc(SZ_4K);

	s_printf(txt_buf, "#FF8000 USB大容量儲存#\n\n#C7EA46 裝置:# ");

	if (usbs->type == MMC_SD)
	{
		switch (usbs->partition)
		{
		case 0:
			strcat(txt_buf, "SD卡");
			break;
		case EMMC_GPP + 1:
			strcat(txt_buf, "emuMMC GPP");
			break;
		case EMMC_BOOT0 + 1:
			strcat(txt_buf, "emuMMC BOOT0");
			break;
		case EMMC_BOOT1 + 1:
			strcat(txt_buf, "emuMMC BOOT1");
			break;
		}
	}
	else
	{
		switch (usbs->partition)
		{
		case EMMC_GPP + 1:
			strcat(txt_buf, "eMMC GPP");
			break;
		case EMMC_BOOT0 + 1:
			strcat(txt_buf, "eMMC BOOT0");
			break;
		case EMMC_BOOT1 + 1:
			strcat(txt_buf, "eMMC BOOT1");
			break;
		}
	}

	lv_mbox_set_text(mbox, txt_buf);
	free(txt_buf);

	lv_obj_t *lbl_status = lv_label_create(mbox, NULL);
	lv_label_set_recolor(lbl_status, true);
	lv_label_set_text(lbl_status, " ");
	usbs->label = (void *)lbl_status;

	lv_obj_t *lbl_tip = lv_label_create(mbox, NULL);
	lv_label_set_recolor(lbl_tip, true);
	if (!usbs->ro)
	{
		if (usbs->type == MMC_SD)
		{
			lv_label_set_static_text(lbl_tip,
				"提示: 如果想要結束, 請在作業系統端 #C7EA46 安全彈出#.\n"
				"       #FFDD00 不要直接拔掉線纜!#");
		}
		else
		{
			lv_label_set_static_text(lbl_tip,
				"提示: 如果想要結束, 請在作業系統端 #C7EA46 安全彈出#.\n"
				"       #FFDD00 如果沒有正常彈出, 你可能需要拔掉線纜!#");
		}
	}
	else
	{
		lv_label_set_static_text(lbl_tip,
			"提示: 如果想要結束, 請在作業系統端 #C7EA46 安全彈出#\n"
			"       或者拔掉線纜!#");
	}
	lv_obj_set_style(lbl_tip, &hint_small_style);

	lv_mbox_add_btns(mbox, mbox_btn_map, mbox_action);
	lv_obj_set_width(mbox, LV_HOR_RES / 9 * 5);
	lv_obj_align(mbox, NULL, LV_ALIGN_CENTER, 0, 0);
	lv_obj_set_top(mbox, true);

	// Dim backlight.
	display_backlight_brightness(20, 1000);

	usb_device_gadget_ums(usbs);

	// Restore backlight.
	display_backlight_brightness(h_cfg.backlight - 20, 1000);

	lv_mbox_add_btns(mbox, mbox_btn_map2, mbox_action);

	ums_mbox = dark_bg;

	return LV_RES_OK;
}

static lv_res_t _create_mbox_ums_error(int error)
{
	lv_obj_t *dark_bg = lv_obj_create(lv_scr_act(), NULL);
	lv_obj_set_style(dark_bg, &mbox_darken);
	lv_obj_set_size(dark_bg, LV_HOR_RES, LV_VER_RES);

	static const char *mbox_btn_map[] = { "\251", "\222確定", "\251", "" };
	lv_obj_t * mbox = lv_mbox_create(dark_bg, NULL);
	lv_mbox_set_recolor_text(mbox, true);

	switch (error)
	{
	case 1:
		lv_mbox_set_text(mbox, "#FF8000 USB大容量儲存#\n\n#FFFF00 掛載SD卡錯誤!#");
		break;
	case 2:
		lv_mbox_set_text(mbox, "#FF8000 USB大容量儲存#\n\n#FFFF00 無可用emuMMC!#");
		break;
	case 3:
		lv_mbox_set_text(mbox, "#FF8000 USB大容量儲存#\n\n#FFFF00 emuMMC未使用分割槽!#");
		break;
	}

	lv_mbox_add_btns(mbox, mbox_btn_map, mbox_action);
	lv_obj_set_width(mbox, LV_HOR_RES / 9 * 5);
	lv_obj_align(mbox, NULL, LV_ALIGN_CENTER, 0, 0);
	lv_obj_set_top(mbox, true);

	return LV_RES_OK;
}

static void usb_gadget_set_text(void *lbl, const char *text)
{
	lv_label_set_text((lv_obj_t *)lbl, text);
	manual_system_maintenance(true);
}

static lv_res_t _action_hid_jc(lv_obj_t *btn)
{
	// Reduce BPMP, RAM and backlight and power off SDMMC1 to conserve power.
	sd_end();
	minerva_change_freq(FREQ_800);
	bpmp_clk_rate_relaxed(true);
	display_backlight_brightness(10, 1000);

	usb_ctxt_t usbs;
	usbs.type = USB_HID_GAMEPAD;
	usbs.system_maintenance = &manual_system_maintenance;
	usbs.set_text = &usb_gadget_set_text;

	_create_mbox_hid(&usbs);

	// Restore BPMP, RAM and backlight.
	minerva_change_freq(FREQ_1600);
	bpmp_clk_rate_relaxed(false);
	display_backlight_brightness(h_cfg.backlight - 20, 1000);

	return LV_RES_OK;
}

/*
static lv_res_t _action_hid_touch(lv_obj_t *btn)
{
	// Reduce BPMP, RAM and backlight and power off SDMMC1 to conserve power.
	sd_end();
	minerva_change_freq(FREQ_800);
	bpmp_clk_rate_relaxed(true);
	display_backlight_brightness(10, 1000);

	usb_ctxt_t usbs;
	usbs.type = USB_HID_TOUCHPAD;
	usbs.system_maintenance = &manual_system_maintenance;
	usbs.set_text = &usb_gadget_set_text;

	_create_mbox_hid(&usbs);

	// Restore BPMP, RAM and backlight.
	minerva_change_freq(FREQ_1600);
	bpmp_clk_rate_relaxed(false);
	display_backlight_brightness(h_cfg.backlight - 20, 1000);

	return LV_RES_OK;
}
*/

static bool usb_msc_emmc_read_only;
lv_res_t action_ums_sd(lv_obj_t *btn)
{
	usb_ctxt_t usbs;
	usbs.type = MMC_SD;
	usbs.partition = 0;
	usbs.offset = 0;
	usbs.sectors = 0;
	usbs.ro = 0;
	usbs.system_maintenance = &manual_system_maintenance;
	usbs.set_text = &usb_gadget_set_text;

	_create_mbox_ums(&usbs);

	return LV_RES_OK;
}

static lv_res_t _action_ums_emmc_boot0(lv_obj_t *btn)
{
	if (!nyx_emmc_check_battery_enough())
		return LV_RES_OK;

	usb_ctxt_t usbs;
	usbs.type = MMC_EMMC;
	usbs.partition = EMMC_BOOT0 + 1;
	usbs.offset = 0;
	usbs.sectors = 0;
	usbs.ro = usb_msc_emmc_read_only;
	usbs.system_maintenance = &manual_system_maintenance;
	usbs.set_text = &usb_gadget_set_text;

	_create_mbox_ums(&usbs);

	return LV_RES_OK;
}

static lv_res_t _action_ums_emmc_boot1(lv_obj_t *btn)
{
	if (!nyx_emmc_check_battery_enough())
		return LV_RES_OK;

	usb_ctxt_t usbs;
	usbs.type = MMC_EMMC;
	usbs.partition = EMMC_BOOT1 + 1;
	usbs.offset = 0;
	usbs.sectors = 0;
	usbs.ro = usb_msc_emmc_read_only;
	usbs.system_maintenance = &manual_system_maintenance;
	usbs.set_text = &usb_gadget_set_text;

	_create_mbox_ums(&usbs);

	return LV_RES_OK;
}

static lv_res_t _action_ums_emmc_gpp(lv_obj_t *btn)
{
	if (!nyx_emmc_check_battery_enough())
		return LV_RES_OK;

	usb_ctxt_t usbs;
	usbs.type = MMC_EMMC;
	usbs.partition = EMMC_GPP + 1;
	usbs.offset = 0;
	usbs.sectors = 0;
	usbs.ro = usb_msc_emmc_read_only;
	usbs.system_maintenance = &manual_system_maintenance;
	usbs.set_text = &usb_gadget_set_text;

	_create_mbox_ums(&usbs);

	return LV_RES_OK;
}

static lv_res_t _action_ums_emuemmc_boot0(lv_obj_t *btn)
{
	if (!nyx_emmc_check_battery_enough())
		return LV_RES_OK;

	usb_ctxt_t usbs;

	int error = !sd_mount();
	if (!error)
	{
		emummc_cfg_t emu_info;
		load_emummc_cfg(&emu_info);

		error = 2;
		if (emu_info.enabled)
		{
			error = 3;
			if (emu_info.sector)
			{
				error = 0;
				usbs.offset = emu_info.sector;
			}
		}

		if (emu_info.path)
			free(emu_info.path);
		if (emu_info.nintendo_path)
			free(emu_info.nintendo_path);
	}
	sd_unmount();

	if (error)
		_create_mbox_ums_error(error);
	else
	{
		usbs.type = MMC_SD;
		usbs.partition = EMMC_BOOT0 + 1;
		usbs.sectors = 0x2000; // Forced 4MB.
		usbs.ro = usb_msc_emmc_read_only;
		usbs.system_maintenance = &manual_system_maintenance;
		usbs.set_text = &usb_gadget_set_text;
		_create_mbox_ums(&usbs);
	}

	return LV_RES_OK;
}

static lv_res_t _action_ums_emuemmc_boot1(lv_obj_t *btn)
{
	if (!nyx_emmc_check_battery_enough())
		return LV_RES_OK;

	usb_ctxt_t usbs;

	int error = !sd_mount();
	if (!error)
	{
		emummc_cfg_t emu_info;
		load_emummc_cfg(&emu_info);

		error = 2;
		if (emu_info.enabled)
		{
			error = 3;
			if (emu_info.sector)
			{
				error = 0;
				usbs.offset = emu_info.sector + 0x2000;
			}
		}

		if (emu_info.path)
			free(emu_info.path);
		if (emu_info.nintendo_path)
			free(emu_info.nintendo_path);
	}
	sd_unmount();

	if (error)
		_create_mbox_ums_error(error);
	else
	{
		usbs.type = MMC_SD;
		usbs.partition = EMMC_BOOT1 + 1;
		usbs.sectors = 0x2000; // Forced 4MB.
		usbs.ro = usb_msc_emmc_read_only;
		usbs.system_maintenance = &manual_system_maintenance;
		usbs.set_text = &usb_gadget_set_text;
		_create_mbox_ums(&usbs);
	}

	return LV_RES_OK;
}

static lv_res_t _action_ums_emuemmc_gpp(lv_obj_t *btn)
{
	if (!nyx_emmc_check_battery_enough())
		return LV_RES_OK;

	usb_ctxt_t usbs;

	int error = !sd_mount();
	if (!error)
	{
		emummc_cfg_t emu_info;
		load_emummc_cfg(&emu_info);

		error = 2;
		if (emu_info.enabled)
		{
			error = 3;
			if (emu_info.sector)
			{
				error = 1;
				usbs.offset = emu_info.sector + 0x4000;

				u8 *gpt = malloc(SD_BLOCKSIZE);
				if (sdmmc_storage_read(&sd_storage, usbs.offset + 1, 1, gpt))
				{
					if (!memcmp(gpt, "EFI PART", 8))
					{
						error = 0;
						usbs.sectors = *(u32 *)(gpt + 0x20) + 1; // Backup LBA + 1.
					}
				}
			}
		}

		if (emu_info.path)
			free(emu_info.path);
		if (emu_info.nintendo_path)
			free(emu_info.nintendo_path);
	}
	sd_unmount();

	if (error)
		_create_mbox_ums_error(error);
	else
	{
		usbs.type = MMC_SD;
		usbs.partition = EMMC_GPP + 1;
		usbs.ro = usb_msc_emmc_read_only;
		usbs.system_maintenance = &manual_system_maintenance;
		usbs.set_text = &usb_gadget_set_text;
		_create_mbox_ums(&usbs);
	}

	return LV_RES_OK;
}

void nyx_run_ums(void *param)
{
	u32 *cfg = (u32 *)param;

	u8 type = (*cfg) >> 24;
	*cfg = *cfg & (~NYX_CFG_EXTRA);

	// Disable read only flag.
	usb_msc_emmc_read_only = false;

	switch (type)
	{
	case NYX_UMS_SD_CARD:
		action_ums_sd(NULL);
		break;
	case NYX_UMS_EMMC_BOOT0:
		_action_ums_emmc_boot0(NULL);
		break;
	case NYX_UMS_EMMC_BOOT1:
		_action_ums_emmc_boot1(NULL);
		break;
	case NYX_UMS_EMMC_GPP:
		_action_ums_emmc_gpp(NULL);
		break;
	case NYX_UMS_EMUMMC_BOOT0:
		_action_ums_emuemmc_boot0(NULL);
		break;
	case NYX_UMS_EMUMMC_BOOT1:
		_action_ums_emuemmc_boot1(NULL);
		break;
	case NYX_UMS_EMUMMC_GPP:
		_action_ums_emuemmc_gpp(NULL);
		break;
	}
}

static lv_res_t _emmc_read_only_toggle(lv_obj_t *btn)
{
	nyx_generic_onoff_toggle(btn);

	usb_msc_emmc_read_only = lv_btn_get_state(btn) & LV_BTN_STATE_TGL_REL ? 1 : 0;

	return LV_RES_OK;
}

static lv_res_t _create_window_usb_tools(lv_obj_t *parent)
{
	lv_obj_t *win = nyx_create_standard_window(SYMBOL_USB" USB工具");

	static lv_style_t h_style;
	lv_style_copy(&h_style, &lv_style_transp);
	h_style.body.padding.inner = 0;
	h_style.body.padding.hor = LV_DPI - (LV_DPI / 4);
	h_style.body.padding.ver = LV_DPI / 9;

	// Create USB Mass Storage container.
	lv_obj_t *h1 = lv_cont_create(win, NULL);
	lv_cont_set_style(h1, &h_style);
	lv_cont_set_fit(h1, false, true);
	lv_obj_set_width(h1, (LV_HOR_RES / 9) * 5);
	lv_obj_set_click(h1, false);
	lv_cont_set_layout(h1, LV_LAYOUT_OFF);

	lv_obj_t *label_sep = lv_label_create(h1, NULL);
	lv_label_set_static_text(label_sep, "");

	lv_obj_t *label_txt = lv_label_create(h1, NULL);
	lv_label_set_static_text(label_txt, "USB大容量儲存");
	lv_obj_set_style(label_txt, lv_theme_get_current()->label.prim);
	lv_obj_align(label_txt, label_sep, LV_ALIGN_OUT_BOTTOM_LEFT, LV_DPI / 4, -LV_DPI * 3 / 10);

	lv_obj_t *line_sep = lv_line_create(h1, NULL);
	static const lv_point_t line_pp[] = { {0, 0}, { LV_HOR_RES - (LV_DPI - (LV_DPI / 4)) * 2, 0} };
	lv_line_set_points(line_sep, line_pp, 2);
	lv_line_set_style(line_sep, lv_theme_get_current()->line.decor);
	lv_obj_align(line_sep, label_txt, LV_ALIGN_OUT_BOTTOM_LEFT, -(LV_DPI / 4), LV_DPI / 8);

	// Create SD UMS button.
	lv_obj_t *btn1 = lv_btn_create(h1, NULL);
	lv_obj_t *label_btn = lv_label_create(btn1, NULL);
	lv_btn_set_fit(btn1, true, true);
	lv_label_set_static_text(label_btn, SYMBOL_SD"  SD卡");

	lv_obj_align(btn1, line_sep, LV_ALIGN_OUT_BOTTOM_LEFT, LV_DPI / 4, LV_DPI / 4);
	lv_btn_set_action(btn1, LV_BTN_ACTION_CLICK, action_ums_sd);

	lv_obj_t *label_txt2 = lv_label_create(h1, NULL);
	lv_label_set_recolor(label_txt2, true);
	lv_label_set_static_text(label_txt2,
		"允許你掛載SD卡到電腦或手機.\n"
		"#C7EA46 支援所有的作業系統. 訪問許可權為# #FF8000 讀/寫.#");

	lv_obj_set_style(label_txt2, &hint_small_style);
	lv_obj_align(label_txt2, btn1, LV_ALIGN_OUT_BOTTOM_LEFT, 0, LV_DPI / 3);

	// Create RAW GPP button.
	lv_obj_t *btn_gpp = lv_btn_create(h1, btn1);
	label_btn = lv_label_create(btn_gpp, NULL);
	lv_label_set_static_text(label_btn, SYMBOL_CHIP"  eMMC原始GPP");
	lv_obj_align(btn_gpp, label_txt2, LV_ALIGN_OUT_BOTTOM_LEFT, 0, LV_DPI / 2);
	lv_btn_set_action(btn_gpp, LV_BTN_ACTION_CLICK, _action_ums_emmc_gpp);

	// Create BOOT0 button.
	lv_obj_t *btn_boot0 = lv_btn_create(h1, btn1);
	label_btn = lv_label_create(btn_boot0, NULL);
	lv_label_set_static_text(label_btn, "BOOT0");
	lv_obj_align(btn_boot0, btn_gpp, LV_ALIGN_OUT_RIGHT_MID, LV_DPI / 10, 0);
	lv_btn_set_action(btn_boot0, LV_BTN_ACTION_CLICK, _action_ums_emmc_boot0);

	// Create BOOT1 button.
	lv_obj_t *btn_boot1 = lv_btn_create(h1, btn1);
	label_btn = lv_label_create(btn_boot1, NULL);
	lv_label_set_static_text(label_btn, "BOOT1");
	lv_obj_align(btn_boot1, btn_boot0, LV_ALIGN_OUT_RIGHT_MID, LV_DPI / 10, 0);
	lv_btn_set_action(btn_boot1, LV_BTN_ACTION_CLICK, _action_ums_emmc_boot1);

	// Create emuMMC RAW GPP button.
	lv_obj_t *btn_emu_gpp = lv_btn_create(h1, btn1);
	label_btn = lv_label_create(btn_emu_gpp, NULL);
	lv_label_set_static_text(label_btn, SYMBOL_MODULES_ALT"  emu原始GPP");
	lv_obj_align(btn_emu_gpp, btn_gpp, LV_ALIGN_OUT_BOTTOM_LEFT, 0, LV_DPI / 2);
	lv_btn_set_action(btn_emu_gpp, LV_BTN_ACTION_CLICK, _action_ums_emuemmc_gpp);

	// Create emuMMC BOOT0 button.
	lv_obj_t *btn_emu_boot0 = lv_btn_create(h1, btn1);
	label_btn = lv_label_create(btn_emu_boot0, NULL);
	lv_label_set_static_text(label_btn, "BOOT0");
	lv_obj_align(btn_emu_boot0, btn_boot0, LV_ALIGN_OUT_BOTTOM_LEFT, 0, LV_DPI / 2);
	lv_btn_set_action(btn_emu_boot0, LV_BTN_ACTION_CLICK, _action_ums_emuemmc_boot0);

	// Create emuMMC BOOT1 button.
	lv_obj_t *btn_emu_boot1 = lv_btn_create(h1, btn1);
	label_btn = lv_label_create(btn_emu_boot1, NULL);
	lv_label_set_static_text(label_btn, "BOOT1");
	lv_obj_align(btn_emu_boot1, btn_boot1, LV_ALIGN_OUT_BOTTOM_LEFT, 0, LV_DPI / 2);
	lv_btn_set_action(btn_emu_boot1, LV_BTN_ACTION_CLICK, _action_ums_emuemmc_boot1);

	label_txt2 = lv_label_create(h1, NULL);
	lv_label_set_recolor(label_txt2, true);
	lv_label_set_static_text(label_txt2,
		"允許你掛載eMMC或emuMMC.\n"
		"#C7EA46 預設訪問許可權為# #FF8000 只讀.#");
	lv_obj_set_style(label_txt2, &hint_small_style);
	lv_obj_align(label_txt2, btn_emu_gpp, LV_ALIGN_OUT_BOTTOM_LEFT, 0, LV_DPI / 3);

	lv_obj_t *h_write = lv_cont_create(win, NULL);
	lv_cont_set_style(h_write, &h_style);
	lv_cont_set_fit(h_write, false, true);
	lv_obj_set_width(h_write, (LV_HOR_RES / 9) * 2);
	lv_obj_set_click(h_write, false);
	lv_cont_set_layout(h_write, LV_LAYOUT_OFF);
	lv_obj_align(h_write, label_txt2, LV_ALIGN_OUT_RIGHT_MID, LV_DPI / 10, 0);

	// Create read/write access button.
	lv_obj_t *btn_write_access = lv_btn_create(h_write, NULL);
	nyx_create_onoff_button(lv_theme_get_current(), h_write,
		btn_write_access, SYMBOL_EDIT" 只讀", _emmc_read_only_toggle, false);
	if (!n_cfg.ums_emmc_rw)
		lv_btn_set_state(btn_write_access, LV_BTN_STATE_TGL_REL);
	_emmc_read_only_toggle(btn_write_access);

	// Create USB Input Devices container.
	lv_obj_t *h2 = lv_cont_create(win, NULL);
	lv_cont_set_style(h2, &h_style);
	lv_cont_set_fit(h2, false, true);
	lv_obj_set_width(h2, (LV_HOR_RES / 9) * 3);
	lv_obj_set_click(h2, false);
	lv_cont_set_layout(h2, LV_LAYOUT_OFF);
	lv_obj_align(h2, h1, LV_ALIGN_OUT_RIGHT_TOP, LV_DPI * 17 / 29, 0);

	label_sep = lv_label_create(h2, NULL);
	lv_label_set_static_text(label_sep, "");

	lv_obj_t *label_txt3 = lv_label_create(h2, NULL);
	lv_label_set_static_text(label_txt3, "USB輸入裝置");
	lv_obj_set_style(label_txt3, lv_theme_get_current()->label.prim);
	lv_obj_align(label_txt3, label_sep, LV_ALIGN_OUT_BOTTOM_LEFT, LV_DPI / 4, -LV_DPI * 4 / 21);

	line_sep = lv_line_create(h2, line_sep);
	lv_obj_align(line_sep, label_txt3, LV_ALIGN_OUT_BOTTOM_LEFT, -(LV_DPI / 4), LV_DPI / 8);

	// Create Gamepad button.
	lv_obj_t *btn3 = lv_btn_create(h2, NULL);
	label_btn = lv_label_create(btn3, NULL);
	lv_btn_set_fit(btn3, true, true);
	lv_label_set_static_text(label_btn, SYMBOL_CIRCUIT"  手柄");
	lv_obj_align(btn3, line_sep, LV_ALIGN_OUT_BOTTOM_LEFT, LV_DPI / 4, LV_DPI / 4);
	lv_btn_set_action(btn3, LV_BTN_ACTION_CLICK, _action_hid_jc);

	lv_obj_t *label_txt4 = lv_label_create(h2, NULL);
	lv_label_set_recolor(label_txt4, true);
	lv_label_set_static_text(label_txt4,
		"插入Joy-Con手柄並將其變成\n"
		"PC或者手機的手柄裝置.\n"
		"#C7EA46 需要兩個Joy-Con都能正常工作.#");

	lv_obj_set_style(label_txt4, &hint_small_style);
	lv_obj_align(label_txt4, btn3, LV_ALIGN_OUT_BOTTOM_LEFT, 0, LV_DPI / 3);
/*
	// Create Touchpad button.
	lv_obj_t *btn4 = lv_btn_create(h2, btn1);
	label_btn = lv_label_create(btn4, NULL);
	lv_label_set_static_text(label_btn, SYMBOL_KEYBOARD"  Touchpad");
	lv_obj_align(btn4, label_txt4, LV_ALIGN_OUT_BOTTOM_LEFT, 0, LV_DPI / 2);
	lv_btn_set_action(btn4, LV_BTN_ACTION_CLICK, _action_hid_touch);
	lv_btn_set_state(btn4, LV_BTN_STATE_INA);

	label_txt4 = lv_label_create(h2, NULL);
	lv_label_set_recolor(label_txt4, true);
	lv_label_set_static_text(label_txt4,
		"Control the PC via the device\'s touchscreen.\n"
		"#C7EA46 Two fingers tap acts like a# #FF8000 Right click##C7EA46 .#\n");
	lv_obj_set_style(label_txt4, &hint_small_style);
	lv_obj_align(label_txt4, btn4, LV_ALIGN_OUT_BOTTOM_LEFT, 0, LV_DPI / 3);
*/
	return LV_RES_OK;
}

static int _fix_attributes(lv_obj_t *lb_val, char *path, u32 *total)
{
	FRESULT res;
	DIR dir;
	u32 dirLength = 0;
	static FILINFO fno;

	// Open directory.
	res = f_opendir(&dir, path);
	if (res != FR_OK)
		return res;

	dirLength = strlen(path);

	// Hard limit path to 1024 characters. Do not result to error.
	if (dirLength > 1024)
	{
		total[2]++;
		goto out;
	}

	for (;;)
	{
		// Clear file or folder path.
		path[dirLength] = 0;

		// Read a directory item.
		res = f_readdir(&dir, &fno);

		// Break on error or end of dir.
		if (res != FR_OK || fno.fname[0] == 0)
			break;

		// Set new directory or file.
		memcpy(&path[dirLength], "/", 1);
		strcpy(&path[dirLength + 1], fno.fname);

		// Is it a directory?
		if (fno.fattrib & AM_DIR)
		{
			// Check if it's a HOS single file folder.
			strcat(path, "/00");
			bool is_hos_special = !f_stat(path, NULL);
			path[strlen(path) - 3] = 0;

			// Set archive bit to HOS single file folders.
			if (is_hos_special)
			{
				if (!(fno.fattrib & AM_ARC))
				{
					if (!f_chmod(path, AM_ARC, AM_ARC))
						total[0]++;
					else
						total[3]++;
				}
			}
			else if (fno.fattrib & AM_ARC) // If not, clear the archive bit.
			{
				if (!f_chmod(path, 0, AM_ARC))
					total[1]++;
				else
					total[3]++;
			}

			lv_label_set_text(lb_val, path);
			manual_system_maintenance(true);

			// Enter the directory.
			res = _fix_attributes(lb_val, path, total);
			if (res != FR_OK)
				break;
		}
	}

out:
	f_closedir(&dir);

	return res;
}

static lv_res_t _create_window_unset_abit_tool(lv_obj_t *btn)
{
	lv_obj_t *win = nyx_create_standard_window(SYMBOL_COPY" 修復歸檔位(所有資料夾)");

	// Disable buttons.
	nyx_window_toggle_buttons(win, true);

	lv_obj_t *desc = lv_cont_create(win, NULL);
	lv_obj_set_size(desc, LV_HOR_RES * 10 / 11, LV_VER_RES - (LV_DPI * 11 / 7) * 4);

	lv_obj_t * lb_desc = lv_label_create(desc, NULL);
	lv_label_set_long_mode(lb_desc, LV_LABEL_LONG_BREAK);
	lv_label_set_recolor(lb_desc, true);

	if (!sd_mount())
	{
		lv_label_set_text(lb_desc, "#FFDD00 初始化SD卡失敗!#");
		lv_obj_set_width(lb_desc, lv_obj_get_width(desc));
	}
	else
	{
		lv_label_set_text(lb_desc, "#00DDFF 遍歷SD卡所有檔案!#\n這可能需要一些時間...");
		lv_obj_set_width(lb_desc, lv_obj_get_width(desc));

		lv_obj_t *val = lv_cont_create(win, NULL);
		lv_obj_set_size(val, LV_HOR_RES * 10 / 11, LV_VER_RES - (LV_DPI * 11 / 7) * 4);

		lv_obj_t * lb_val = lv_label_create(val, lb_desc);

		char *path = malloc(0x1000);
		path[0] = 0;

		lv_label_set_text(lb_val, "");
		lv_obj_set_width(lb_val, lv_obj_get_width(val));
		lv_obj_align(val, desc, LV_ALIGN_OUT_BOTTOM_LEFT, 0, 0);

		u32 total[4] = { 0 };
		_fix_attributes(lb_val, path, total);

		sd_unmount();

		lv_obj_t *desc2 = lv_cont_create(win, NULL);
		lv_obj_set_size(desc2, LV_HOR_RES * 10 / 11, LV_VER_RES - (LV_DPI * 11 / 7) * 4);
		lv_obj_t * lb_desc2 = lv_label_create(desc2, lb_desc);

		char *txt_buf = (char *)malloc(0x500);

		if (!total[0] && !total[1])
			s_printf(txt_buf, "#96FF00 完成! 無需更改.#");
		else
			s_printf(txt_buf, "#96FF00 完成! 歸檔位修復:# #FF8000 %d 未設定且 %d 已設定!#", total[1], total[0]);

		// Check errors.
		if (total[2] || total[3])
		{
			s_printf(txt_buf, "\n\n#FFDD00 錯誤: 訪問目錄數: %d, 歸檔位修復數: %d!#\n"
					          "#FFDD00 請檢查檔案系統是否有錯誤.#",
					          total[2], total[3]);
		}

		lv_label_set_text(lb_desc2, txt_buf);
		lv_obj_set_width(lb_desc2, lv_obj_get_width(desc2));
		lv_obj_align(desc2, val, LV_ALIGN_OUT_BOTTOM_RIGHT, 0, 0);

		free(path);
	}

	// Enable buttons.
	nyx_window_toggle_buttons(win, false);

	return LV_RES_OK;
}

static lv_res_t _create_mbox_fix_touchscreen(lv_obj_t *btn)
{
	int res = 0;
	lv_obj_t *dark_bg = lv_obj_create(lv_scr_act(), NULL);
	lv_obj_set_style(dark_bg, &mbox_darken);
	lv_obj_set_size(dark_bg, LV_HOR_RES, LV_VER_RES);

	static const char *mbox_btn_map[] = { "\251", "\222確定", "\251", "" };
	lv_obj_t * mbox = lv_mbox_create(dark_bg, NULL);
	lv_mbox_set_recolor_text(mbox, true);

	char *txt_buf = malloc(SZ_16K);
	strcpy(txt_buf, "#FF8000 請不要觸控式螢幕幕!#\n\n調整過程將在");
	u32 text_idx = strlen(txt_buf);
	lv_mbox_set_text(mbox, txt_buf);

	lv_obj_set_width(mbox, LV_HOR_RES / 9 * 6);
	lv_obj_align(mbox, NULL, LV_ALIGN_CENTER, 0, 0);
	lv_obj_set_top(mbox, true);

	lv_mbox_set_text(mbox,
		"#FFDD00 警告: 僅在觸控式螢幕有問題時才需執行!#\n\n"
		"按#FF8000 電源鍵# 繼續.\n按 #FF8000 音量鍵# 中止.");
	manual_system_maintenance(true);

	if (!(btn_wait() & BTN_POWER))
		goto out;

	manual_system_maintenance(true);
	lv_mbox_set_text(mbox, txt_buf);

	u32 seconds = 5;
	while (seconds)
	{
		s_printf(txt_buf + text_idx, "%d 秒後開始...", seconds);
		lv_mbox_set_text(mbox, txt_buf);
		manual_system_maintenance(true);
		msleep(1000);
		seconds--;
	}

	u8 err[2];
	if (!touch_panel_ito_test(err))
		goto ito_failed;

	if (!err[0] && !err[1])
	{
		res = touch_execute_autotune();
		if (res)
			goto out;
	}
	else
	{
		touch_sense_enable();

		s_printf(txt_buf, "#FFFF00 ITO測試: ");
		switch (err[0])
		{
		case ITO_FORCE_OPEN:
			strcat(txt_buf, "力應開路");
			break;
		case ITO_SENSE_OPEN:
			strcat(txt_buf, "感應開路");
			break;
		case ITO_FORCE_SHRT_GND:
			strcat(txt_buf, "力應短路到地");
			break;
		case ITO_SENSE_SHRT_GND:
			strcat(txt_buf, "感應短路到地");
			break;
		case ITO_FORCE_SHRT_VCM:
			strcat(txt_buf, "力應短路到VDD");
			break;
		case ITO_SENSE_SHRT_VCM:
			strcat(txt_buf, "感應短路到VDD");
			break;
		case ITO_FORCE_SHRT_FORCE:
			strcat(txt_buf, "力應短路到力應");
			break;
		case ITO_SENSE_SHRT_SENSE:
			strcat(txt_buf, "感應短路到感應");
			break;
		case ITO_F2E_SENSE:
			strcat(txt_buf, "力應短路到感應");
			break;
		case ITO_FPC_FORCE_OPEN:
			strcat(txt_buf, "FPC力應開路");
			break;
		case ITO_FPC_SENSE_OPEN:
			strcat(txt_buf, "FPC感應開路");
			break;
		default:
			strcat(txt_buf, "未知");
			break;

		}
		s_printf(txt_buf + strlen(txt_buf), " (%d), 通道: %d#\n\n", err[0], err[1]);
		strcat(txt_buf, "#FFFF00 觸控式螢幕校準失敗!");
		lv_mbox_set_text(mbox, txt_buf);
		goto out2;
	}

ito_failed:
	touch_sense_enable();

out:
	if (res)
		lv_mbox_set_text(mbox, "#C7EA46 觸控式螢幕校準完成!");
	else
		lv_mbox_set_text(mbox, "#FFFF00 觸控式螢幕校準失敗!");

out2:
	lv_mbox_add_btns(mbox, mbox_btn_map, mbox_action);

	free(txt_buf);

	return LV_RES_OK;
}

static lv_res_t _create_window_dump_pk12_tool(lv_obj_t *btn)
{
	lv_obj_t *win = nyx_create_standard_window(SYMBOL_MODULES" 提取package1/2");

	// Disable buttons.
	nyx_window_toggle_buttons(win, true);

	lv_obj_t *desc = lv_cont_create(win, NULL);
	lv_obj_set_size(desc, LV_HOR_RES * 10 / 11, LV_VER_RES - (LV_DPI * 12 / 7));

	lv_obj_t * lb_desc = lv_label_create(desc, NULL);
	lv_obj_set_style(lb_desc, &monospace_text);
	lv_label_set_long_mode(lb_desc, LV_LABEL_LONG_BREAK);
	lv_label_set_recolor(lb_desc, true);
	lv_obj_set_width(lb_desc, lv_obj_get_width(desc));

	if (!sd_mount())
	{
		lv_label_set_text(lb_desc, "#FFDD00 SD卡初始化失敗!#");

		goto out_end;
	}

	char path[128];

	u8 kb = 0;
	u8 *pkg1 = (u8 *)zalloc(SZ_256K);
	u8 *warmboot = (u8 *)zalloc(SZ_256K);
	u8 *secmon = (u8 *)zalloc(SZ_256K);
	u8 *loader = (u8 *)zalloc(SZ_256K);
	u8 *pkg2 = NULL;

	char *txt_buf  = (char *)malloc(SZ_16K);

	if (!emmc_initialize(false))
	{
		lv_label_set_text(lb_desc, "#FFDD00 eMMC初始化失敗!#");

		goto out_free;
	}

	emmc_set_partition(EMMC_BOOT0);

	// Read package1.
	static const u32 BOOTLOADER_SIZE          = SZ_256K;
	static const u32 BOOTLOADER_MAIN_OFFSET   = 0x100000;
	static const u32 HOS_KEYBLOBS_OFFSET      = 0x180000;

	char *build_date = malloc(32);
	u32 pk1_offset =  h_cfg.t210b01 ? sizeof(bl_hdr_t210b01_t) : 0; // Skip T210B01 OEM header.
	sdmmc_storage_read(&emmc_storage, BOOTLOADER_MAIN_OFFSET / EMMC_BLOCKSIZE, BOOTLOADER_SIZE / EMMC_BLOCKSIZE, pkg1);

	const pkg1_id_t *pkg1_id = pkg1_identify(pkg1 + pk1_offset, build_date);

	s_printf(txt_buf, "#00DDFF 找到pkg1('%s')#\n\n", build_date);
	free(build_date);
	lv_label_set_text(lb_desc, txt_buf);
	manual_system_maintenance(true);

	// Dump package1 in its encrypted state.
	emmcsn_path_impl(path, "/pkg1", "pkg1_enc.bin", &emmc_storage);
	bool res = sd_save_to_file(pkg1, BOOTLOADER_SIZE, path);

	// Exit if unknown.
	if (!pkg1_id)
	{
		strcat(txt_buf, "#FFDD00 未知pkg1版本!#");
		lv_label_set_text(lb_desc, txt_buf);
		manual_system_maintenance(true);

		if (!res)
		{
			strcat(txt_buf, "\n加密的pkg1提取到了pkg1_enc.bin");
			lv_label_set_text(lb_desc, txt_buf);
			manual_system_maintenance(true);
		}

		goto out_free;
	}

	kb = pkg1_id->kb;

	tsec_ctxt_t tsec_ctxt = {0};
	tsec_ctxt.fw = (void *)(pkg1 + pkg1_id->tsec_off);
	tsec_ctxt.pkg1 = (void *)pkg1;
	tsec_ctxt.pkg11_off = pkg1_id->pkg11_off;

	// Read keyblob.
	u8 *keyblob = (u8 *)zalloc(EMMC_BLOCKSIZE);
	sdmmc_storage_read(&emmc_storage, HOS_KEYBLOBS_OFFSET / EMMC_BLOCKSIZE + kb, 1, keyblob);

	// Decrypt.
	hos_keygen(keyblob, kb, &tsec_ctxt);
	free(keyblob);

	if (h_cfg.t210b01 || kb <= HOS_KB_VERSION_600)
	{
		if (!pkg1_decrypt(pkg1_id, pkg1))
		{
			strcat(txt_buf, "#FFDD00 Pkg1解密失敗!#\n");
			if (h_cfg.t210b01)
				strcat(txt_buf, "#FFDD00 BEK丟失?#\n");
			lv_label_set_text(lb_desc, txt_buf);
			goto out_free;
		}
	}

	if (h_cfg.t210b01 || kb <= HOS_KB_VERSION_620)
	{
		pkg1_unpack(warmboot, secmon, loader, pkg1_id, pkg1 + pk1_offset);
		pk11_hdr_t *hdr_pk11 = (pk11_hdr_t *)(pkg1 + pk1_offset + pkg1_id->pkg11_off + 0x20);

		// Display info.
		s_printf(txt_buf + strlen(txt_buf),
			"#C7EA46 NX Bootloader大小:  #0x%05X\n"
			"#C7EA46 Secure monitor地址: #0x%05X\n"
			"#C7EA46 Secure monitor大小: #0x%05X\n"
			"#C7EA46 Warmboot地址:       #0x%05X\n"
			"#C7EA46 Warmboot大小:       #0x%05X\n\n",
			hdr_pk11->ldr_size, pkg1_id->secmon_base, hdr_pk11->sm_size, pkg1_id->warmboot_base, hdr_pk11->wb_size);

		lv_label_set_text(lb_desc, txt_buf);
		manual_system_maintenance(true);

		// Dump package1.1.
		emmcsn_path_impl(path, "/pkg1", "pkg1_decr.bin", &emmc_storage);
		if (sd_save_to_file(pkg1, SZ_256K, path))
			goto out_free;
		strcat(txt_buf, "pkg1提取到了pkg1_decr.bin\n");
		lv_label_set_text(lb_desc, txt_buf);
		manual_system_maintenance(true);

		// Dump nxbootloader.
		emmcsn_path_impl(path, "/pkg1", "nxloader.bin", &emmc_storage);
		if (sd_save_to_file(loader, hdr_pk11->ldr_size, path))
			goto out_free;
		strcat(txt_buf, "NX Bootloader提取到了nxloader.bin\n");
		lv_label_set_text(lb_desc, txt_buf);
		manual_system_maintenance(true);

		// Dump secmon.
		emmcsn_path_impl(path, "/pkg1", "secmon.bin", &emmc_storage);
		if (sd_save_to_file(secmon, hdr_pk11->sm_size, path))
			goto out_free;
		strcat(txt_buf, "Secure Monitor提取到了secmon.bin\n");
		lv_label_set_text(lb_desc, txt_buf);
		manual_system_maintenance(true);

		// Dump warmboot.
		emmcsn_path_impl(path, "/pkg1", "warmboot.bin", &emmc_storage);
		if (sd_save_to_file(warmboot, hdr_pk11->wb_size, path))
			goto out_free;
		// If T210B01, save a copy of decrypted warmboot binary also.
		if (h_cfg.t210b01)
		{

			se_aes_iv_clear(13);
			se_aes_crypt_cbc(13, DECRYPT, warmboot + 0x330, hdr_pk11->wb_size - 0x330,
				warmboot + 0x330, hdr_pk11->wb_size - 0x330);
			emmcsn_path_impl(path, "/pkg1", "warmboot_dec.bin", &emmc_storage);
			if (sd_save_to_file(warmboot, hdr_pk11->wb_size, path))
				goto out_free;
		}
		strcat(txt_buf, "Warmboot提取到了warmboot.bin\n\n");
		lv_label_set_text(lb_desc, txt_buf);
		manual_system_maintenance(true);
	}

	// Dump package2.1.
	emmc_set_partition(EMMC_GPP);
	// Parse eMMC GPT.
	LIST_INIT(gpt);
	emmc_gpt_parse(&gpt);
	// Find package2 partition.
	emmc_part_t *pkg2_part = emmc_part_find(&gpt, "BCPKG2-1-Normal-Main");
	if (!pkg2_part)
		goto out;

	// Read in package2 header and get package2 real size.
	u8 *tmp = (u8 *)malloc(EMMC_BLOCKSIZE);
	emmc_part_read(pkg2_part, 0x4000 / EMMC_BLOCKSIZE, 1, tmp);
	u32 *hdr_pkg2_raw = (u32 *)(tmp + 0x100);
	u32 pkg2_size = hdr_pkg2_raw[0] ^ hdr_pkg2_raw[2] ^ hdr_pkg2_raw[3];
	free(tmp);
	// Read in package2.
	u32 pkg2_size_aligned = ALIGN(pkg2_size, EMMC_BLOCKSIZE);
	pkg2 = malloc(pkg2_size_aligned);
	emmc_part_read(pkg2_part, 0x4000 / EMMC_BLOCKSIZE,
		pkg2_size_aligned / EMMC_BLOCKSIZE, pkg2);

	// Dump encrypted package2.
	emmcsn_path_impl(path, "/pkg2", "pkg2_encr.bin", &emmc_storage);
	res = sd_save_to_file(pkg2, pkg2_size, path);

	// Decrypt package2 and parse KIP1 blobs in INI1 section.
	pkg2_hdr_t *pkg2_hdr = pkg2_decrypt(pkg2, kb);
	if (!pkg2_hdr)
	{
		strcat(txt_buf, "#FFDD00 Pkg2解密失敗!#");
		lv_label_set_text(lb_desc, txt_buf);
		manual_system_maintenance(true);

		if (!res)
		{
			strcat(txt_buf, "\n加密的 pkg2提取到了pkg2_encr.bin\n");
			lv_label_set_text(lb_desc, txt_buf);
			manual_system_maintenance(true);
		}

		// Clear EKS slot, in case something went wrong with tsec keygen.
		hos_eks_clear(kb);

		goto out;
	}

	// Display info.
	s_printf(txt_buf + strlen(txt_buf),
		"#C7EA46 系統核心大小:   #0x%05X\n"
		"#C7EA46 INI1程式大小:   #0x%05X\n\n",
		pkg2_hdr->sec_size[PKG2_SEC_KERNEL], pkg2_hdr->sec_size[PKG2_SEC_INI1]);

	lv_label_set_text(lb_desc, txt_buf);
	manual_system_maintenance(true);

	// Dump pkg2.1.
	emmcsn_path_impl(path, "/pkg2", "pkg2_decr.bin", &emmc_storage);
	if (sd_save_to_file(pkg2, pkg2_hdr->sec_size[PKG2_SEC_KERNEL] + pkg2_hdr->sec_size[PKG2_SEC_INI1], path))
		goto out;
	strcat(txt_buf, "pkg2提取到了pkg2_decr.bin\n");
	lv_label_set_text(lb_desc, txt_buf);
	manual_system_maintenance(true);

	// Dump kernel.
	emmcsn_path_impl(path, "/pkg2", "kernel.bin", &emmc_storage);
	if (sd_save_to_file(pkg2_hdr->data, pkg2_hdr->sec_size[PKG2_SEC_KERNEL], path))
		goto out;
	strcat(txt_buf, "Kernel提取到了kernel.bin\n");
	lv_label_set_text(lb_desc, txt_buf);
	manual_system_maintenance(true);

	// Dump INI1.
	u32 ini1_off  = pkg2_hdr->sec_size[PKG2_SEC_KERNEL];
	u32 ini1_size = pkg2_hdr->sec_size[PKG2_SEC_INI1];
	if (!ini1_size)
	{
		pkg2_get_newkern_info(pkg2_hdr->data);
		ini1_off  = pkg2_newkern_ini1_start;
		ini1_size = pkg2_newkern_ini1_end - pkg2_newkern_ini1_start;
	}

	if (!ini1_off)
	{
		strcat(txt_buf, "#FFDD00 提取INI1和kips失敗!#\n");
		goto out;
	}

	pkg2_ini1_t *ini1 = (pkg2_ini1_t *)(pkg2_hdr->data + ini1_off);
	emmcsn_path_impl(path, "/pkg2", "ini1.bin", &emmc_storage);
	if (sd_save_to_file(ini1, ini1_size, path))
		goto out;

	strcat(txt_buf, "INI1提取到了ini1.bin\n\n");
	lv_label_set_text(lb_desc, txt_buf);
	manual_system_maintenance(true);

	char filename[32];
	u8 *ptr = (u8 *)ini1;
	ptr += sizeof(pkg2_ini1_t);

	// Dump all kips.
	u8 *kip_buffer = (u8 *)malloc(SZ_4M);

	for (u32 i = 0; i < ini1->num_procs; i++)
	{
		pkg2_kip1_t *kip1 = (pkg2_kip1_t *)ptr;
		u32 kip1_size = pkg2_calc_kip1_size(kip1);

		s_printf(filename, "%s.kip1", kip1->name);
		if ((u32)kip1 % 8)
		{
			memcpy(kip_buffer, kip1, kip1_size);
			kip1 = (pkg2_kip1_t *)kip_buffer;
		}

		emmcsn_path_impl(path, "/pkg2/ini1", filename, &emmc_storage);
		if (sd_save_to_file(kip1, kip1_size, path))
		{
			free(kip_buffer);
			goto out;
		}

		s_printf(txt_buf + strlen(txt_buf), "%s kip提取到了%s.kip1\n", kip1->name, kip1->name);
		lv_label_set_text(lb_desc, txt_buf);
		manual_system_maintenance(true);

		ptr += kip1_size;
	}
	free(kip_buffer);

out:
	emmc_gpt_free(&gpt);
out_free:
	free(pkg1);
	free(secmon);
	free(warmboot);
	free(loader);
	free(pkg2);
	free(txt_buf);
	emmc_end();
	sd_unmount();

	if (kb >= HOS_KB_VERSION_620)
		se_aes_key_clear(8);
out_end:
	// Enable buttons.
	nyx_window_toggle_buttons(win, false);

	return LV_RES_OK;
}

static void _create_tab_tools_emmc_pkg12(lv_theme_t *th, lv_obj_t *parent)
{
	lv_page_set_scrl_layout(parent, LV_LAYOUT_PRETTY);

	// Create Backup & Restore container.
	lv_obj_t *h1 = _create_container(parent);

	lv_obj_t *label_sep = lv_label_create(h1, NULL);
	lv_label_set_static_text(label_sep, "");

	lv_obj_t *label_txt = lv_label_create(h1, NULL);
	lv_label_set_static_text(label_txt, "備份和恢復");
	lv_obj_set_style(label_txt, th->label.prim);
	lv_obj_align(label_txt, label_sep, LV_ALIGN_OUT_BOTTOM_LEFT, LV_DPI / 4, -LV_DPI * 3 / 10);

	lv_obj_t *line_sep = lv_line_create(h1, NULL);
	static const lv_point_t line_pp[] = { {0, 0}, { LV_HOR_RES - (LV_DPI - (LV_DPI / 4)) * 2, 0} };
	lv_line_set_points(line_sep, line_pp, 2);
	lv_line_set_style(line_sep, th->line.decor);
	lv_obj_align(line_sep, label_txt, LV_ALIGN_OUT_BOTTOM_LEFT, -(LV_DPI / 4), LV_DPI / 8);

	// Create Backup eMMC button.
	lv_obj_t *btn = lv_btn_create(h1, NULL);
	if (hekate_bg)
	{
		lv_btn_set_style(btn, LV_BTN_STYLE_REL, &btn_transp_rel);
		lv_btn_set_style(btn, LV_BTN_STYLE_PR, &btn_transp_pr);
	}
	lv_obj_t *label_btn = lv_label_create(btn, NULL);
	lv_btn_set_fit(btn, true, true);
	lv_label_set_static_text(label_btn, SYMBOL_UPLOAD"  備份eMMC");
	lv_obj_align(btn, line_sep, LV_ALIGN_OUT_BOTTOM_LEFT, LV_DPI / 4, LV_DPI / 4);
	lv_btn_set_action(btn, LV_BTN_ACTION_CLICK, create_window_backup_restore_tool);

	lv_obj_t *label_txt2 = lv_label_create(h1, NULL);
	lv_label_set_recolor(label_txt2, true);
	lv_label_set_static_text(label_txt2,
		"允許您將 eMMC 分割槽單獨或作為整個原始映象\n"
		"備份到 SD 卡.\n"
		"#C7EA46 支援# #FF8000 4GB# #C7EA46 及以上SD卡. #"
		"#FF8000 FAT32# #C7EA46 和 ##FF8000 exFAT##C7EA46 檔案系統.#");
	lv_obj_set_style(label_txt2, &hint_small_style);
	lv_obj_align(label_txt2, btn, LV_ALIGN_OUT_BOTTOM_LEFT, 0, LV_DPI / 3);

	// Create Restore eMMC button.
	lv_obj_t *btn2 = lv_btn_create(h1, btn);
	label_btn = lv_label_create(btn2, NULL);
	lv_label_set_static_text(label_btn, SYMBOL_DOWNLOAD"  恢復eMMC");
	lv_obj_align(btn2, label_txt2, LV_ALIGN_OUT_BOTTOM_LEFT, 0, LV_DPI / 2);
	lv_btn_set_action(btn2, LV_BTN_ACTION_CLICK, create_window_backup_restore_tool);

	label_txt2 = lv_label_create(h1, NULL);
	lv_label_set_recolor(label_txt2, true);
	lv_label_set_static_text(label_txt2,
		"允許您單獨恢復 eMMC或emuMMC 分割槽\n"
		"或從SD卡恢復整個原始映象.\n"
		"#C7EA46 支援# #FF8000 4GB# #C7EA46 及以上SD卡. #"
		"#FF8000 FAT32# #C7EA46 和 ##FF8000 exFAT##C7EA46 檔案系統.#");
	lv_obj_set_style(label_txt2, &hint_small_style);
	lv_obj_align(label_txt2, btn2, LV_ALIGN_OUT_BOTTOM_LEFT, 0, LV_DPI / 3);

	// Create Misc container.
	lv_obj_t *h2 = _create_container(parent);
	lv_obj_align(h2, h1, LV_ALIGN_OUT_RIGHT_TOP, 0, 0);

	label_sep = lv_label_create(h2, NULL);
	lv_label_set_static_text(label_sep, "");

	lv_obj_t *label_txt3 = lv_label_create(h2, NULL);
	lv_label_set_static_text(label_txt3, "SD分割槽與USB");
	lv_obj_set_style(label_txt3, th->label.prim);
	lv_obj_align(label_txt3, label_sep, LV_ALIGN_OUT_BOTTOM_LEFT, LV_DPI / 4, -LV_DPI * 3 / 10);

	line_sep = lv_line_create(h2, line_sep);
	lv_obj_align(line_sep, label_txt3, LV_ALIGN_OUT_BOTTOM_LEFT, -(LV_DPI / 4), LV_DPI / 8);

	// Create Partition SD Card button.
	lv_obj_t *btn3 = lv_btn_create(h2, NULL);
	if (hekate_bg)
	{
		lv_btn_set_style(btn3, LV_BTN_STYLE_REL, &btn_transp_rel);
		lv_btn_set_style(btn3, LV_BTN_STYLE_PR, &btn_transp_pr);
	}
	label_btn = lv_label_create(btn3, NULL);
	lv_btn_set_fit(btn3, true, true);
	lv_label_set_static_text(label_btn, SYMBOL_SD"  SD卡分割槽管理");
	lv_obj_align(btn3, line_sep, LV_ALIGN_OUT_BOTTOM_LEFT, LV_DPI / 4, LV_DPI / 4);
	lv_btn_set_action(btn3, LV_BTN_ACTION_CLICK, create_window_partition_manager);

	lv_obj_t *label_txt4 = lv_label_create(h2, NULL);
	lv_label_set_recolor(label_txt4, true);
	lv_label_set_static_text(label_txt4,
		"允許您對SD卡進行分割槽以便與 #C7EA46 emuMMC#,\n"
		"#C7EA46 Android# 和 #C7EA46 Linux# 一起使用. 你也可以直接刷入Linux和Android.\n");
	lv_obj_set_style(label_txt4, &hint_small_style);
	lv_obj_align(label_txt4, btn3, LV_ALIGN_OUT_BOTTOM_LEFT, 0, LV_DPI / 3);

	label_sep = lv_label_create(h2, NULL);
	lv_label_set_static_text(label_sep, "");
	lv_obj_align(label_sep, label_txt4, LV_ALIGN_OUT_BOTTOM_LEFT, 0, LV_DPI * 11 / 7);

	// Create USB Tools button.
	lv_obj_t *btn4 = lv_btn_create(h2, btn3);
	label_btn = lv_label_create(btn4, NULL);
	lv_label_set_static_text(label_btn, SYMBOL_USB"  USB工具");
	lv_obj_align(btn4, label_txt4, LV_ALIGN_OUT_BOTTOM_LEFT, 0, LV_DPI / 2);
	lv_btn_set_action(btn4, LV_BTN_ACTION_CLICK, _create_window_usb_tools);

	label_txt4 = lv_label_create(h2, NULL);
	lv_label_set_recolor(label_txt4, true);
	lv_label_set_static_text(label_txt4,
		"#C7EA46 USB大容量儲存#, #C7EA46 手柄# 和其他USB工具.\n"
		"大容量儲存可以掛載SD卡, eMMC 和 emuMMC.\n"
		"手柄可以將Switch轉變為輸入裝置.#");
	lv_obj_set_style(label_txt4, &hint_small_style);
	lv_obj_align(label_txt4, btn4, LV_ALIGN_OUT_BOTTOM_LEFT, 0, LV_DPI / 3);
}

static void _create_tab_tools_arc_autorcm(lv_theme_t *th, lv_obj_t *parent)
{
	lv_page_set_scrl_layout(parent, LV_LAYOUT_PRETTY);

	// Create Misc container.
	lv_obj_t *h1 = _create_container(parent);

	lv_obj_t *label_sep = lv_label_create(h1, NULL);
	lv_label_set_static_text(label_sep, "");

	lv_obj_t *label_txt = lv_label_create(h1, NULL);
	lv_label_set_static_text(label_txt, "雜項");
	lv_obj_set_style(label_txt, th->label.prim);
	lv_obj_align(label_txt, label_sep, LV_ALIGN_OUT_BOTTOM_LEFT, LV_DPI / 4, -LV_DPI * 3 / 10);

	lv_obj_t *line_sep = lv_line_create(h1, NULL);
	static const lv_point_t line_pp[] = { {0, 0}, { LV_HOR_RES - (LV_DPI - (LV_DPI / 4)) * 2, 0} };
	lv_line_set_points(line_sep, line_pp, 2);
	lv_line_set_style(line_sep, th->line.decor);
	lv_obj_align(line_sep, label_txt, LV_ALIGN_OUT_BOTTOM_LEFT, -(LV_DPI / 4), LV_DPI / 8);

	// Create fix archive bit button.
	lv_obj_t *btn = lv_btn_create(h1, NULL);
	if (hekate_bg)
	{
		lv_btn_set_style(btn, LV_BTN_STYLE_REL, &btn_transp_rel);
		lv_btn_set_style(btn, LV_BTN_STYLE_PR, &btn_transp_pr);
	}
	lv_obj_t *label_btn = lv_label_create(btn, NULL);
	lv_btn_set_fit(btn, true, true);
	lv_label_set_static_text(label_btn, SYMBOL_DIRECTORY"  修復歸檔位");
	lv_obj_align(btn, line_sep, LV_ALIGN_OUT_BOTTOM_LEFT, LV_DPI / 4, LV_DPI / 4);
	lv_btn_set_action(btn, LV_BTN_ACTION_CLICK, _create_window_unset_abit_tool);

	lv_obj_t *label_txt2 = lv_label_create(h1, NULL);
	lv_label_set_recolor(label_txt2, true);
	lv_label_set_static_text(label_txt2,
		"允許您修復所有資料夾的歸檔位, 包括\n"
		"根目錄和emuMMC的\'Nintendo\'資料夾.\n"
		"#C7EA46 它將歸檔位設定為以 ##FF8000 .[ext]# 命名的資料夾\n"
		"#FF8000 當您有損壞訊息時使用該選項.#");
	lv_obj_set_style(label_txt2, &hint_small_style);
	lv_obj_align(label_txt2, btn, LV_ALIGN_OUT_BOTTOM_LEFT, 0, LV_DPI / 3);

	// Create Fix touch calibration button.
	lv_obj_t *btn2 = lv_btn_create(h1, btn);
	label_btn = lv_label_create(btn2, NULL);
	lv_label_set_static_text(label_btn, SYMBOL_KEYBOARD"  校準觸控式螢幕");
	lv_obj_align(btn2, label_txt2, LV_ALIGN_OUT_BOTTOM_LEFT, 0, LV_DPI / 2);
	lv_btn_set_action(btn2, LV_BTN_ACTION_CLICK, _create_mbox_fix_touchscreen);

	label_txt2 = lv_label_create(h1, NULL);
	lv_label_set_recolor(label_txt2, true);
	lv_label_set_static_text(label_txt2,
		"允許您校準觸控式螢幕模組.\n"
		"#FF8000 這可以解決Nyx和官方系統中觸控式螢幕的任何問題.#");
	lv_obj_set_style(label_txt2, &hint_small_style);
	lv_obj_align(label_txt2, btn2, LV_ALIGN_OUT_BOTTOM_LEFT, 0, LV_DPI / 3);

	// Create Others container.
	lv_obj_t *h2 = _create_container(parent);
	lv_obj_align(h2, h1, LV_ALIGN_OUT_RIGHT_TOP, 0, 0);

	label_sep = lv_label_create(h2, NULL);
	lv_label_set_static_text(label_sep, "");

	lv_obj_t *label_txt3 = lv_label_create(h2, NULL);
	lv_label_set_static_text(label_txt3, "其他");
	lv_obj_set_style(label_txt3, th->label.prim);
	lv_obj_align(label_txt3, label_sep, LV_ALIGN_OUT_BOTTOM_LEFT, LV_DPI / 4, -LV_DPI * 3 / 10);

	line_sep = lv_line_create(h2, line_sep);
	lv_obj_align(line_sep, label_txt3, LV_ALIGN_OUT_BOTTOM_LEFT, -(LV_DPI / 4), LV_DPI / 8);

	// Create AutoRCM On/Off button.
	lv_obj_t *btn3 = lv_btn_create(h2, NULL);
	if (hekate_bg)
	{
		lv_btn_set_style(btn3, LV_BTN_STYLE_REL, &btn_transp_rel);
		lv_btn_set_style(btn3, LV_BTN_STYLE_PR, &btn_transp_pr);
		lv_btn_set_style(btn3, LV_BTN_STYLE_TGL_REL, &btn_transp_tgl_rel);
		lv_btn_set_style(btn3, LV_BTN_STYLE_TGL_PR, &btn_transp_tgl_pr);
	}
	label_btn = lv_label_create(btn3, NULL);
	lv_btn_set_fit(btn3, true, true);
	lv_label_set_recolor(label_btn, true);
	lv_label_set_text(label_btn, SYMBOL_REFRESH"  AutoRCM #00FFC9   ON #");
	lv_obj_align(btn3, line_sep, LV_ALIGN_OUT_BOTTOM_LEFT, LV_DPI / 4, LV_DPI / 4);
	lv_btn_set_action(btn3, LV_BTN_ACTION_CLICK, _create_mbox_autorcm_status);

	// Set default state for AutoRCM and lock it out if patched unit.
	if (get_set_autorcm_status(false))
		lv_btn_set_state(btn3, LV_BTN_STATE_TGL_REL);
	else
		lv_btn_set_state(btn3, LV_BTN_STATE_REL);
	nyx_generic_onoff_toggle(btn3);

	if (h_cfg.rcm_patched)
	{
		lv_obj_set_click(btn3, false);
		lv_btn_set_state(btn3, LV_BTN_STATE_INA);
	}
	autorcm_btn = btn3;

	char *txt_buf = (char *)malloc(SZ_4K);

	s_printf(txt_buf,
		"允許您在不使用 #C7EA46 音量+# 和 #C7EA46 HOME# (jig) 的情況下進入RCM.\n"
		"#FF8000 它可以在需要時恢復所有版本的AutoRCM.#\n"
		"#FF3C28 這會破壞BCT, 如果沒有自定義引導載入程式#\n"
		"#FF3C28 您將無法啟動.#");

	if (h_cfg.rcm_patched)
		strcat(txt_buf, "#FF8000 此裝置已修復RCM漏洞, 本選項禁用!#");

	lv_obj_t *label_txt4 = lv_label_create(h2, NULL);
	lv_label_set_recolor(label_txt4, true);
	lv_label_set_text(label_txt4, txt_buf);
	free(txt_buf);

	lv_obj_set_style(label_txt4, &hint_small_style);
	lv_obj_align(label_txt4, btn3, LV_ALIGN_OUT_BOTTOM_LEFT, 0, LV_DPI / 3);

	label_sep = lv_label_create(h2, NULL);
	lv_label_set_static_text(label_sep, "");
	lv_obj_align(label_sep, label_txt4, LV_ALIGN_OUT_BOTTOM_LEFT, 0, LV_DPI * 11 / 7);

	// Create Dump Package1/2 button.
	lv_obj_t *btn4 = lv_btn_create(h2, btn);
	label_btn = lv_label_create(btn4, NULL);
	lv_label_set_static_text(label_btn, SYMBOL_MODULES"  提取Package1/2");
	lv_obj_align(btn4, label_txt4, LV_ALIGN_OUT_BOTTOM_LEFT, 0, LV_DPI / 2);
	lv_btn_set_action(btn4, LV_BTN_ACTION_CLICK, _create_window_dump_pk12_tool);

	label_txt2 = lv_label_create(h2, NULL);
	lv_label_set_recolor(label_txt2, true);
	lv_label_set_static_text(label_txt2,
		"允許您提取和解密 pkg1 和 pkg2\n"
		"並進一步將其拆分為單獨的部分. 它還能提取kip1.");
	lv_obj_set_style(label_txt2, &hint_small_style);
	lv_obj_align(label_txt2, btn4, LV_ALIGN_OUT_BOTTOM_LEFT, 0, LV_DPI / 3);
}

void create_tab_tools(lv_theme_t *th, lv_obj_t *parent)
{
	lv_obj_t *tv = lv_tabview_create(parent, NULL);

	lv_obj_set_size(tv, LV_HOR_RES, 572);

	static lv_style_t tabview_style;
	lv_style_copy(&tabview_style, th->tabview.btn.rel);
	tabview_style.body.padding.ver = LV_DPI / 8;

	lv_tabview_set_style(tv, LV_TABVIEW_STYLE_BTN_REL, &tabview_style);
	if (hekate_bg)
	{
		lv_tabview_set_style(tv, LV_TABVIEW_STYLE_BTN_PR, &tabview_btn_pr);
		lv_tabview_set_style(tv, LV_TABVIEW_STYLE_BTN_TGL_PR, &tabview_btn_tgl_pr);
	}

	lv_tabview_set_sliding(tv, false);
	lv_tabview_set_btns_pos(tv, LV_TABVIEW_BTNS_POS_BOTTOM);

	lv_obj_t *tab1= lv_tabview_add_tab(tv, "eMMC "SYMBOL_DOT" SD 分割槽 "SYMBOL_DOT" USB");
	lv_obj_t *tab2 = lv_tabview_add_tab(tv, "歸檔位 "SYMBOL_DOT" RCM "SYMBOL_DOT" 觸控 "SYMBOL_DOT" Pkg1/2");

	lv_obj_t *line_sep = lv_line_create(tv, NULL);
	static const lv_point_t line_pp[] = { {0, 0}, { 0, LV_DPI / 4} };
	lv_line_set_points(line_sep, line_pp, 2);
	lv_line_set_style(line_sep, lv_theme_get_current()->line.decor);
	lv_obj_align(line_sep, tv, LV_ALIGN_IN_BOTTOM_MID, -1, -LV_DPI * 2 / 12);

	_create_tab_tools_emmc_pkg12(th, tab1);
	_create_tab_tools_arc_autorcm(th, tab2);

	lv_tabview_set_tab_act(tv, 0, false);
}
