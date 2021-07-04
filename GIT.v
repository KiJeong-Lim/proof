Require Import Coq.micromega.Lia.

Module mu.

Inductive ord : Set :=
| Ze : ord
| Sc : ord -> ord
| Lm : (nat -> ord) -> ord
.



End mu.
