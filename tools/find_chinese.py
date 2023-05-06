import re
import sys
import os

allChineseWords = set({})

paths = ['../nyx/nyx_gui/frontend/', '../bdk/usb/']
for path in paths:
    for filename in os.listdir(path):
        if filename.endswith('.c'):
            with open(path + filename, encoding='utf-8') as file:
                content = file.read()
                ll = re.findall('[\u4e00-\u9fa5]', content)
                for w in ll:
                    allChineseWords.add(w)

allChineseWords.update(set(list("識別大氣層偵安卓懷舊冠大氣層系統人傅宇大門原")))
wordList = list(allChineseWords)
wordList.sort()
for w in wordList:
    print(w, end="")
print("\n")