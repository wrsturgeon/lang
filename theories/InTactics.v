From Coq Require Export
  List.
Export ListNotations.

Ltac auto_in := repeat (try (left; reflexivity); right); fail.
Example auto_in_12345 : In 3 [1;2;3;4;5]. Proof. auto_in. Qed.
Example auto_in_12345_fail : In 9 [1;2;3;4;5]. Proof. Fail auto_in. Abort.

Ltac not_in H := repeat (destruct H as [H | H]; [discriminate H |]); contradiction H.
Example not_in_12345 : ~In 9 [1;2;3;4;5]. Proof. intro C. not_in C. Qed.
Example not_in_12345_fail : ~In 3 [1;2;3;4;5]. Proof. intro C. Fail not_in C. Abort.
