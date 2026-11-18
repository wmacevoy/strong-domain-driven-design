# Queue

What is being worked, in what order, by whom, and what would make it done. The shared cursor
([SE1/W10](https://github.com/wmacevoy/software-engineering/blob/v1.7/guide/08-work.md#w10)).
Only the owner sets an item to done.

| # | Item | Versioned requirement IDs (or *chore*) | Owner | Done when | Estimate (number / range / time box) | Status | Since |
| - | ---- | ---------------------------- | ----- | --------- | ------------------------------------ | ------ | ----- |
| 1 | The owner reads `REQUIREMENTS_v1.md`, a draft, and says what is wrong with it | REQ1 | Warren | each *(inferred)* mark is confirmed or struck, and each *Not yet answered* has an answer or a date | time box: 1 hour | ready | 2026-11-18 |
| 2 | The STUN model compared with gosh's own `stun_parse`, in the check | REQ1/DOM-2 | agent | `tools/check.sh` runs gosh's real function and the model on the same seeded answers and on gosh's fuzz corpus, fails if they differ, and is seen to fail on a model changed to differ | range: half a day to a day (it was done once by hand on 2026-11-17, outside any repository) | blocked: on where gosh's source is read from (design, *Deferred*) | 2026-11-18 |
| 3 | Each model says when gosh's file has changed since it was written | REQ1/DOM-3 | agent | the check prints a warning naming the model and both commits when `src/pathfinding/stun.h` differs from the commit the model names, and is seen to do so | time box: half a day | blocked: on the same | 2026-11-18 |
| 4 | The map: every boundary of gosh where bytes or calls come in from outside | REQ1/MAP-1 | agent | the README's table lists each, with the file and function in gosh, and the owner has said which are assumed | range: 1 to 2 days | ready | 2026-11-18 |
| 5 | One deliberate change to the parser, to measure how much of the proof it makes untrue | REQ1/LRN-1 | agent | a finding gives the lines of claims changed for a named change to the model, and the time to prove it again | time box: half a day | ready | 2026-11-18 |
| 6 | The generator reads calls from one method to another, and to another domain | REQ1 *Deferred*; SHAPE-4 ("it makes correct calls") | agent | in oopc: a model with a call is proved, what is owed states what the callee needs, and a call that breaks it is seen to fail | range: 2 to 5 days | ready | 2026-11-18 |
| 7 | A second domain of gosh | REQ1/DOM-1, REQ1/RED-1, REQ1/LRN-1 | agent | proved, seen red, and a finding says what it suggests about gosh's shape | unknown until the map exists | blocked: on 4, and the owner's choice | 2026-11-18 |
| 8 | Hosting: this repository, oopc's branch and its licence, CI | chore | Warren | the owner has said where this is hosted; oopc's `explore/proof-compiler` is pushed or not, on his word; a fresh clone passes the check | time box: 1 hour, after the decisions | blocked: on the owner | 2026-11-18 |
