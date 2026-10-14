---
source_url: https://mncore-challenge.preferred.jp/problem/fizzbuzz
slug: fizzbuzz
fetched_at: 2026-10-14T00:39:05+00:00
---

# FizzBuzz

- Top: 98 lines / tails
- Par: 400 lines

## Problem Statement

\(1\) から \(6334\) までの各整数について
* \(15\) の倍数なら `FizzBuzz`
* \(5\) の倍数でなく \(3\) の倍数なら `Fizz`
* \(3\) の倍数でなく \(5\) の倍数なら `Buzz`
* それ以外ならそのままの数字
とし、さらにそれらを `\n` 区切りで連結した文字列を、Group=\(0\) の DRAM の先頭から書き込んでください。
最後に `\n` を付加する必要はなく、ヌル終端の必要もありません。
例えば、仮に \(1\) から \(3\) までであれば、文字列は `1\n2\nFizz` なので、 `0x310A320A46697A7A` の \(8\) バイトを書き込めばよいことになります。

## Outputs

* String `$d[0:4096]@0`, `/((4096:1, 8_W:1))`

## Testcases

* [testcase.vsm](https://mncore-challenge.preferred.jp/testcase/fizzbuzz/testcase.vsm)
