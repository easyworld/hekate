import re
import sys
import os


allChineseWords = set({})

for filename in os.listdir("../nyx/nyx_gui/frontend"):
    if filename.endswith('.c'):
        with open('../nyx/nyx_gui/frontend/' + filename, encoding='utf-8') as file:
            content = file.read()
            ll = re.findall('[\u4e00-\u9fa5]', content)
            for w in ll:
                allChineseWords.add(w)

# allChineseWords.update(set(list("识别大气层侦安卓怀旧提醒大家软件完全免费不要付费购买")))
wordList = list(allChineseWords)
wordList.sort()
for w in wordList:
    print(w, end="")
print("\n")
