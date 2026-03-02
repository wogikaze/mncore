---
title: wogikaze
id: 66b35d9fff0097001dac23a6
created_unix: 1723030944
updated_unix: 1723545196
views: 33
---

# wogikaze

<https://lh3.googleusercontent.com/a/ACg8ocIuw7RqWcWS12YNWF-puFp0ApV4zWw_DO6JeymUkqdA8v0f0mdX=s96-c#.png>

ここはwogikazeのページです[[Cosense Beaver.icon]]

```script.js
import "/api/code/yuyasurarin/wogikaze/出張用.js";
import '/api/code/progfay-pub/Replace_Text_UserScript/script.js'
scrapbox.PopupMenu.addButton({
  title: (text) => /[\n．.。]/.test(text) ? "\\n" : "",
  onClick: (text) => text
    .replace(/(\w)\n(\w)/g, "$1 $2")
    .replaceAll("\n", "")
    .replaceAll("．", "．\n")
    .replaceAll(".", ".\n")
    .replaceAll("。", "。\n"),
});

```
[[omakase-link-script]]
```script.js
// based on https://scrapbox.io/daiiz/omakase-links

// 既に記法になっているなどの理由で、置換すべきでない範囲を取得する
const detectLocked = text => {
    const syntax = /\[(\/\w|[^\[!"#%&'()\*\+,\-\.\/\{\|\}<>_~])[^\[\]]*\]/g;
    const locked = text.split('').map(_ => false)
    const matches = text.matchAll(syntax);
    for (const match of matches) {
  		locked.fill(true, match.index, match.index + match[0].length);
    }
  	return locked;
}

const escapeRegExp = string =>string.replace(/[.*+?^=!:${}()|[\]\/\\]/g, '\\$&');

const autoLink = text => {
  	if (!text) return;
	
	// リンクを長い順に並べる
  	const titles = scrapbox.Project.pages.map(p => p.title)
        .filter(title => title.length > 2)  // 3文字以下のタイトルを除外する
        .sort((a, b) => b.length - a.length);

  	const locked = detectLocked(text)
  	const matched = text.split('').map(_ => null)
  	
  	const allNull = arr => arr.every(x => x === null);
  
  	for (const title of titles) {
    	const regexp = new RegExp(escapeRegExp(title), 'gi');
    	const matches = text.matchAll(regexp);
    	for (const match of matches) {
      		const len = match[0].length;
      		const idx = match.index;
      		if (allNull(matched.slice(idx, idx + len)) && !locked[idx]) {
        		for (let i = 0; i < len; i++) {
          			let c = text[idx + i];
          			if (i === 0) c = `[${c}`;
          			if (i === len - 1) c = `${c}]`;
          			matched[idx + i] = c;
        		}
      		}
    	}
  	}
  
  	// 無駄にテロメアがupdateされるのを防ぐ為、何も置換しない時は何も返さない
  	if (allNull(matched)) return
  	// 配列matchedでnullの位置を、元のtextの文字に置き換える
  	return matched.map((c, idx) => c ?? text[idx]).join('')
}

scrapbox.PopupMenu.addButton({
  title: '[✨]',
  onClick: autoLink
})


```
