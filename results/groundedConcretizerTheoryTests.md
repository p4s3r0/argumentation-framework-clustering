## Theory that spurious grounded Concretizer Set infers spuriousness for every Subset 

**Arguments** $\rightarrow$ Amount of arguments in the AF.

**Attacks** $\rightarrow$ Amount of attacks in the AF. This can vary, since same attacks can be applied twice.

**Amount** $\rightarrow$ Amount of tests executed.

**Skipped** $\rightarrow$ Amount of tests which were skipped due to two factors: 1. Abstract AF is faithful with grounded concretizer list. 2. Amount of subsets too big.

**Passed** $\rightarrow$ Amount of tests where grounded concretizer set was spurious and all the subsets were spurious as well.

**Failed** $\rightarrow$ Amount of tests where grounded concretizer set was spurious and atleast one of the subsets was faithful.

|Arguments|Attacks|Amount|Skipped|Passed|Failed|
|---|---|---|---|---|---|
|5| 5|500|383|116| 1|
|5| 6|500|398|109| 2|
|5| 7|500|411| 87| 2|
|5| 8|500|394|102| 4|
|5| 9|500|417| 83| 0|
|5|10|500|406| 94| 0|
|5|11|500|414| 86| 0|
|6| 7|500|405| 87| 8|
|6| 8|500|407| 84| 9|
|6| 9|500|396|100| 4|
|6|10|500|413| 82| 5|
|6|11|500|416| 79| 5|
|6|12|500|432| 67| 1|
|7| 9|500|414| 73|13|
|7|10|500|426| 68| 6|
|7|11|500|404| 88| 8|
---
