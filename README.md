# hekate - Nyx

![Hekate图片](https://user-images.githubusercontent.com/3665130/60391760-bc1e8c00-9afe-11e9-8b7a-b065873081b2.png)


自定义图形化 Nintendo Switch 引导程序、固件补丁工具及更多实用工具。



- [功能特性](#功能特性)
- [引导程序文件夹和文件](#引导程序文件夹和文件)
- [引导程序配置](#引导程序配置)
  * [hekate 全局配置键/值](#hekate-全局配置键值当条目为config时)
  * [启动条目键/值组合](#启动条目键值组合)
  * [Exosphère 启动条目键/值组合](#exosphère-启动条目键值组合)
  * [Payload 存储](#payload-存储)
  * [Nyx 配置键/值（nyx.ini）](#nyx-配置键值nyxini)



## 功能特性

- **完全可配置的图形界面**，支持触摸屏和 Joycon 输入
- **启动器风格、背景和颜色主题**
- **HOS（Switch 系统）引导程序** —— 支持 CFW 正版系统/虚拟系统、OFW 正版系统和原厂系统
- **Android 和 Linux 引导程序**
- **Payload 启动器**
- **eMMC/emuMMC 备份/恢复工具**
- **SD 卡分区管理器** —— 为 HOS（正版系统/emuMMC）、Android 和 Linux 的任意组合准备和格式化 SD 卡
- **emuMMC 创建和管理器** —— 还可以迁移和修复现有的 emuMMC
- **Switch Android 和 Linux 刷写工具**
- **SD/eMMC/emuMMC 的 USB 大容量存储（UMS）** —— 将 Switch 变为 SD 卡读卡器
- **USB 游戏手柄** —— 将带有 Joycon 的 Switch 变为 USB HID 游戏手柄
- **硬件和外设信息**（SoC、熔丝、RAM、显示屏、触摸屏、eMMC、SD、电池、电源、充电器）
- **许多其他工具**，如存档位修复器、触摸校准、SD/eMMC 基准测试、AutoRCM 启用器等


## 引导程序文件夹和文件

| 文件夹/文件 | 描述 |
| --- | --- |
| bootloader | 主文件夹。 |
|  \|__ bootlogo.bmp | 如果未找到 `logopath` 键则使用。由用户提供。可省略。 |
|  \|__ hekate_ipl.ini | 主引导程序配置和 `启动` 菜单中的启动条目。 |
|  \|__ nyx.ini | Nyx GUI 配置 |
|  \|__ patches.ini | 添加外部补丁。可省略。可在[此处](./res/patches_template.ini)找到模板 |
|  \|__ update.bin | 如果版本较新，则在启动时加载。通常用于芯片。首次启动时自动更新和创建。 |
| bootloader/ini/ | 用于单个 ini 文件。`更多配置` 菜单。支持自动启动。 |
| bootloader/res/ | Nyx 用户资源。图标等。 |
|  \|__ background.bmp | Nyx - 自定义背景。由用户提供。 |
|  \|__ icon_switch.bmp | Nyx - CFW 的默认图标。 |
|  \|__ icon_payload.bmp | Nyx - Payload 的默认图标。 |
| bootloader/sys/ | hekate 和 Nyx 系统模块文件夹。!重要! |
|  \|__ emummc.kipm | emuMMC KIP1 模块。 |
|  \|__ libsys_lp0.bso | LP0（睡眠模式）模块。 |
|  \|__ libsys_minerva.bso | Minerva 训练单元。用于 DRAM 频率训练。 |
|  \|__ nyx.bin | Nyx - hekate 的 GUI。 |
|  \|__ res.pak | Nyx 资源包。 |
|  \|__ thk.bin | Atmosphère Tsec Hovi 密钥生成器。 |
|  \|__ /l4t/ | 包含 L4T（Linux/Android）相关固件的文件夹。 |
| bootloader/screenshots/ | 保存 Nyx 截图的文件夹 |
| bootloader/payloads/ | 用于 `Payloads` 菜单。支持所有 CFW 引导程序、工具、Linux payload。仅当包含在 ini 中时才支持自动启动。 |
| bootloader/libtools/ | 保留 |



## 引导程序配置

引导程序可以通过 `Nyx` -> `选项` 或 'bootloader/hekate_ipl.ini' 进行配置。特殊节 'config' 控制实际的全局配置。任何其他 ini 节代表一个启动条目，只能通过 ini 手动编辑。


共有四种可能的条目类型。"**[ ]**"：启动条目，"**{ }**"：标题，"**#**"：注释，"*换行*"：.ini 的装饰性空行。


**您可以在[此处](./res/hekate_ipl_template.ini)找到模板**


### hekate 全局配置键/值（*[config]*部分）

使用 Nyx 中的 `选项` 编辑以下配置：

| 配置选项 | 描述 |
| --- | --- |
| autoboot=0 | 0：禁用，#：自动启动的启动条目编号。 |
| autoboot_list=0 | 0：从 hekate_ipl.ini 读取 `autoboot` 启动条目，1：从 ini 文件夹读取（ini 文件按 ASCII 排序）。 |
| bootwait=3 | 0：禁用（同时禁用启动 Logo。注入后一直按住 **VOL-** 可进入菜单。），#：等待 **VOL-** 进入菜单的时间。最大：20秒。 |
| autohosoff=1 | 0：禁用，1：如果通过 RTC 闹钟从 HOS 唤醒，显示 Logo 后完全关机，2：不显示 Logo，立即关机。 |
| autonogc=1 | 0：禁用，1：如果发现未烧毁的熔丝且启动 >= 4.0.0 的 HOS，则自动应用 nogc 补丁。 |
| updater2p=0 | 0：禁用，1：强制更新（如需要）reboot2payload 二进制文件为 hekate。 |
| backlight=100 | 屏幕背光级别。0-255。 |
| --- | --------- *以下仅可通过 ini 编辑* --------- |
| noticker=0 | 0：在自定义启动 Logo 期间绘制动画线条，表示跳转到菜单的剩余时间。1：禁用。 |
| bootprotect=0 | 0：禁用，1：通过禁止在 HOS 中读取或编辑来保护 bootloader 文件夹免受损坏。 |


### 启动条目键/值组合

启动条目需要由用户手动添加/编辑所选的键/值组合。

| 配置选项 | 描述 |
| --- | --- |
| warmboot={FILE path} | 替换 warmboot 二进制文件 |
| secmon={FILE path} | 替换安全监视器二进制文件 |
| kernel={FILE path} | 替换内核二进制文件 |
| kip1={FILE path} | 替换/添加内核初始进程。可设置多个。 |
| kip1={FOLDER path}/* | 加载文件夹内的所有 .kip/.kip1 文件。与单个 kip1 键兼容。 |
| pkg3={FILE path} | 接受 Atmosphere `package3` 二进制文件并从中 `提取` 所有需要的部分。包括 kip、exosphere、warmboot 和 mesosphere。 |
| fss0={FILE path} | 同上。!已弃用! |
| pkg3ex=1 | 启用从 PKG3/FSS0 存储加载实验性内容 |
| pkg3kip1skip={KIP name} | 跳过从 `pkg3`/`fss0` 加载的 kip。允许多个，用 `,` 分隔。名称必须与 `PKG3` 中的名称完全匹配。 |
| exofatal={FILE path} | 替换 Mariko 的 exosphere fatal 二进制文件 |
| --- | --- |
| kip1patch=patchname | 启用 kip1 补丁。允许多个，用 `,` 分隔。如果未找到实际补丁，将显示警告。 |
| emupath={FOLDER path} | 强制 emuMMC 使用选定的路径。（=emuMMC/RAW1, =emuMMC/SD00 等）。emuMMC 必须由 hekate 创建，因为它使用 raw_based/file_based 文件。 |
| emummcforce=1 | 强制使用 emuMMC。如果 emummc.ini 被禁用或未找到，则会导致错误。 |
| emummc_force_disable=1 | 如果 emuMMC 已启用，则禁用它。 |
| stock=1 | 通过 hekate 引导程序启动 OFW。在运行原厂系统时禁用不需要的内核补丁和 CFW kip。`如果 emuMMC 已启用，则需要 emummc_force_disable=1`。emuMMC 在原厂系统上不受支持。如果需要 OFW 之外的额外 KIP，可以用 `kip1` 键定义。不应使用依赖 Atmosphère 补丁的 kip，因为会导致卡死。如果需要 `NOGC`，请使用 `kip1patch=nogc`。 |
| fullsvcperm=1 | 禁用 SVC 验证（完全服务权限）。不适用于以 Mesosphere 为内核的情况。 |
| debugmode=1 | 启用调试模式。使用 exosphere 作为 secmon 时已过时。 |
| kernelprocid=1 | 启用原厂内核进程 ID 发送/接收补丁。使用 `pkg3`/`fss0` 时不需要。 |
| --- | --- |
| payload={FILE path} | Payload 启动。工具、Android/Linux、CFW 引导程序等。使用时上述任何键都不生效。 |
| --- | --- |
| l4t=1 | L4T Linux/Android 原生启动。 |
| boot_prefixes={FOLDER path} | L4T 启动栈目录。 |
| ram_oc=0 | L4T RAM 超频。查看 README_CONFIG.txt 获取更多信息。 |
| ram_oc_vdd2=1100 | L4T RAM VDD2 电压。设置 VDD2（T210B01）或 VDD2/VDDQ（T210）电压。1050-1175。 |
| ram_oc_vddq=600 | L4T RAM VDDQ 电压。设置 VDDQ（T210B01）。550-650。 |
| uart_port=0 | 为 L4T uboot/内核启用串口日志。 |
| sld_type=0x31444C53 | 控制无缝显示支持的类型。0x0：禁用，0x31444C53：L4T 无缝显示。 |
| Additional keys | 各发行版支持更多键。查看 README_CONFIG.txt 获取更多信息。 |
| --- | --- |
| bootwait=3 | 覆盖 `[config]` 中的全局 bootwait。 |
| id=IDNAME | 用于通过 ID 强制启动的启动条目标识符。最多 7 个字符。 |
| logopath={FILE path} | 如果存在，将加载指定的位图。否则如果存在 `bootloader/bootlogo.bmp` 将使用它 |
| icon={FILE path} | 强制 Nyx 使用此处定义的图标。如果未找到，将检查以启动条目命名的 bmp（[Test 2] -> `bootloader/res/Test 2.bmp`）。否则使用默认图标。 |


**注意1**：使用通配符（`/*`）搭配 `kip1` 时，仍可在之后使用普通的 `kip1` 加载额外的单个 kip。

**注意2**：使用 PKG3/FSS0 时，它会解析 exosphere、warmboot 和所有核心 kip。您可以在定义 `pkg3`/`fss0` 之后使用 `secmon`/`warmboot` 来覆盖前两个。
您可以使用 `kip1` 加载额外的 kip，或通过通配符（`/*`）加载多个。

**警告**：使用 `kip1` 覆盖 *pkg3/fss0 核心* kip 时请小心。
如果 kip 之间不兼容可能会出问题。如果兼容，则可以无问题地覆盖 `pkg3`/`fss0` 的 kip（适用于测试中间 kip 更改的情况）。在这种情况下，`kip1` 行必须在 `pkg3`/`fss0` 行**之后**。


### Exosphère 启动条目键/值组合

以下内容可与 HOS 启动条目配对使用：

| 配置选项 | 描述 |
| --- | --- |
| nouserexceptions=1 | 与 Exosphère 配对时禁用用户态异常处理器。 |
| userpmu=1 | 与 Exosphère 配对时启用用户态对 PMU 的访问。 |
| cal0blank=1 | 覆盖 Exosphère 配置 `blank_prodinfo_{sys/emu}mmc`。如果该键不存在，将使用 `exosphere.ini`。 |
| cal0writesys=1 | 覆盖 Exosphère 配置 `allow_writing_to_cal_sysmmc`。如果该键不存在，将使用 `exosphere.ini`。 |
| usb3force=1 | 覆盖系统设置 mitm 配置 `usb30_force_enabled`。如果该键不存在，将使用 `system_settings.ini`。 |
| memmode=1 | 为零售设备启用引导配置内存模式。默认情况下，最大 RAM 限制为 4GB。启用后将自动选择大小。 |


**注意**：如上所述，`cal0blank`、`cal0writesys`、`usb3force` 会覆盖 `exosphere.ini` 或 `system_settings.ini`。0：禁用，1：启用，键缺失：使用原始值。


**注意2**：`exosphere.ini` 和 `system_settings.ini` 中的 `blank_prodinfo_{sys/emu}mmc`、`allow_writing_to_cal_sysmmc` 和 `usb30_force_enabled` 分别是唯一可以在 hekate 启动配置外部产生影响的 Atmosphère 配置键，**前提是** hekate 配置中的等效键缺失。


## Payload 存储

hekate 在二进制文件中有一个启动存储，帮助其在 BPMP 环境之外进行配置：

| 偏移 / 名称 | 描述 |
| --- | --- |
| '0x94' boot_cfg | bit0：`强制自动启动`，bit1：`显示启动日志`，bit2：`从 ID 启动`，bit3：`启动到 emuMMC`。 |
| '0x95' autoboot | 如果 `强制自动启动`，0：强制进入菜单，否则启动该条目。 |
| '0x96' autoboot_list | 如果 `强制自动启动` 且有 `autoboot`，则从 ini 文件夹启动。 |
| '0x97' extra_cfg | 当菜单被强制时：bit5：`运行 UMS`。 |
| '0x98' xt_str[128] | 取决于设置的配置位。 |
| '0x98' ums[1] | 当设置 `运行 UMS` 时，将启动选定的 UMS。0：SD，1/2/3：eMMC BOOT0/BOOT1/GPP，4/5/6：emuMMC BOOT0/BOOT1/GPP， |
| '0x98' id[8] | 当设置 `从 ID 启动` 时，将自动搜索所有 ini 并找到具有该 ID 的启动条目并启动。必须以 NULL 结尾。 |
| '0xA0' emummc_path[120] | 当设置 `启动到 emuMMC` 时，将覆盖当前的 emuMMC（启动条目或 emummc.ini）。必须以 NULL 结尾。 |


## Nyx 配置键/值（nyx.ini）

使用 Nyx 中的 `Nyx 设置` 编辑以下配置：

| 配置选项 | 描述 |
| --- | --- |
| themebg=2d2d2d | 以 HEX 设置 Nyx 背景颜色。0x0B0B0B 到 0xC7C7C7。 |
| themecolor=167 | 设置 Nyx 文本高亮颜色。 |
| entries5col=0 | 1：将启动条目列数从每行 4 个设为 5 个。总共 10 个条目。 |
| timeoffset=0 | 以 HEX 设置时区偏移。必须为 epoch 格式 |
| timedst=1 | 启用自动夏令时调整 |
| homescreen=0 | 设置主屏幕。0：主菜单，1：所有配置（合并启动和更多配置），2：启动，3：更多配置。 |
| verification=1 | 0：禁用备份/恢复验证，1：稀疏（基于块，快速且基本可靠），2：完整（基于 sha256，慢但 100% 可靠）。 |
| --- | ----- *以下仅可通过 nyx.ini 编辑* ----- |
| umsemmcrw=0 | 1：eMMC/emuMMC UMS 默认以可写模式挂载。 |
| jcdisable=0 | 1：完全禁用 Joycon 驱动。 |
| jcforceright=0 | 1：强制使用右侧 Joycon 作为主鼠标控制。 |
| bpmpclock=1 | 0：自动，1：589 MHz，2：576 MHz，3：563 MHz，4：544 MHz，5：408 MHz。如果 Nyx 卡死或 UMS/备份验证等功能失败，请使用 2 到 5。 |


```
hekate  (c) 2018,      naehrwert, st4rk.
        (c) 2018-2026, CTCaer.

Nyx GUI (c) 2019-2026, CTCaer.

Thanks to: derrek, nedwill, plutoo, shuffle2, smea, thexyz, yellows8.
Greetings to: fincs, hexkyz, SciresM, Shiny Quagsire, WinterMute.

Open source and free packages used:
 - Littlev Graphics Library,
   Copyright (c) 2016-2018 Gabor Kiss-Vamosi
 - FatFs R0.13c,
   Copyright (c) 2006-2018, ChaN
   Copyright (c) 2018-2022, CTCaer
 - bcl-1.2.0,
   Copyright (c) 2003-2006, Marcus Geelnard
 - blz,
   Copyright (c) 2018, SciresM
 - elfload,
   Copyright (c) 2014 Owen Shepherd,
   Copyright (c) 2018 M4xw

                         ___
                      .-'   `'.
                     /         \
                     |         ;
                     |         |           ___.--,
            _.._     |0) = (0) |    _.---'`__.-( (_.
     __.--'`_.. '.__.\    '--. \_.-' ,.--'`     `""`
    ( ,.--'`   ',__ /./;   ;, '.__.'`    __
    _`) )  .---.__.' / |   |\   \__..--""  """--.,_
   `---' .'.''-._.-'`_./  /\ '.  \ _.--''````'''--._`-.__.'
         | |  .' _.-' |  |  \  \  '.               `----`
          \ \/ .'     \  \   '. '-._)
           \/ /        \  \    `=.__`'-.
           / /\         `) )    / / `"".`\
     , _.-'.'\ \        / /    ( (     / /
      `--'`   ) )    .-'.'      '.'.  | (
             (/`    ( (`          ) )  '-;   [switchbrew]
```
