# mathmatic_in_elementary_number_th


初等数论讲义的形式化证明 by lean


## Contents


### Ch1

- [x] ch1_1

- [ ] ch1_2 

- [x] ch1_3 由 mathlib 实现

- [ ] ch1_4

- [ ] ch1_5


## Ch2



## 形式化证明目标


证明目标选用 青岛大学 刘奎,杨炯老师的英文讲义


## 结构


1. 证明的主体部分在 MathmaticInElementaryNumberTh 中, 按照章节 ch 分类


## 细节


1. 讲义中使用的 `Definition`, 通常用 `def` 表示

2. 因为lean中用来陈述和证明数学命题的关键词 仅有 `theorem`, `lemma`, `example` 无法满足讲义中所使用的 `Proposition` `Corollary` `Theorem` 等需求, 故在证明过程中均用 `theorem` 表示. 而讲义中的 `Lemma`, 在证明过程中使用同名 `lemma` 表示

3. 在 mathlib 中 已有的部分基础命题, 统一使用 mathlib 中给的证明或命题表示
