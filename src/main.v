
Require Import Unicode.Utf8.
Require Import ZArith.

Open Scope Z_scope.

Parameter MaximumInt : Z.

Definition MinimumInt := 1 - MaximumInt.

Print MinimumInt.

