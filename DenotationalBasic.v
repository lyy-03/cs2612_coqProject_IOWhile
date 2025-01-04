Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import Coq.Lists.List. Import ListNotations.
Require Import PL.InductiveType.
Require Import PL.RecurProp.
Require Import PL.Syntax.
Local Open Scope list.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

(** * 简单表达式的指称语义 *)

Module StateModel_SimpleWhile1.
Import Lang_SimpleWhile.

(** 程序状态的定义：*)

Definition state: Type := var_name -> Z.

End StateModel_SimpleWhile1.

Module DntSem_SimpleWhile1.
Import Lang_SimpleWhile
       StateModel_SimpleWhile1.

(** 整数类型表达式的行为：*)

Fixpoint eval_expr_int (e: expr_int) (s: state) : Z :=
  match e with
  | EConst n => n
  | EVar X => s X
  | EAdd e1 e2 => eval_expr_int e1 s + eval_expr_int e2 s
  | ESub e1 e2 => eval_expr_int e1 s - eval_expr_int e2 s
  | EMul e1 e2 => eval_expr_int e1 s * eval_expr_int e2 s
  end.

Notation "⟦ e ⟧" := (eval_expr_int e)
  (at level 0, e custom prog_lang_entry at level 99).

(** 下面是两个具体的例子。*)

Example eval_example1: forall (s: state),
  s "x" = 1 ->
  s "y" = 2 ->
  ⟦ "x" + "y" ⟧ s = 3.
Proof. intros. simpl. rewrite H, H0. reflexivity. Qed.

Example eval_example2: forall (s: state),
  s "x" = 1 ->
  s "y" = 2 ->
  ⟦ "x" * "y" + 1 ⟧ s = 3.
Proof. intros. simpl. rewrite H, H0. reflexivity. Qed.


(** * 行为等价 *)

(** 基于整数类型表达式的语义定义_[eval_expr_int]_，我们可以定义整数类型表达式之
    间的行为等价（亦称语义等价）：两个表达式_[e1]_与_[e2]_是等价的当且仅当它们在
    任何程序状态上的求值结果都相同。*)

Definition iequiv (e1 e2: expr_int): Prop :=
  forall s, ⟦ e1 ⟧ s = ⟦ e2 ⟧ s.

(** 之后我们将在Coq中用_[e1 ~=~ e2]_表示_[iequiv e1 e2]_。*)

Notation "e1 '~=~' e2" := (iequiv e1 e2)
  (at level 69, no associativity).

Example iequiv_sample:
  [["x" + "x"]] ~=~ [["x" * 2]].
Proof.
  intros.
  unfold iequiv.
  intros.
  simpl.
  lia.
Qed.

(** 下面罗列的都是整数类型表达式语义等价的例子。*)

Lemma zero_plus_equiv: forall (a: expr_int),
  [[0 + a]] ~=~ a.
Proof.
  intros.
  unfold iequiv.
  intros.
  simpl.
  lia.
Qed.

Lemma plus_zero_equiv: forall (a: expr_int),
  [[a + 0]] ~=~ a.
Proof.
  intros.
  unfold iequiv.
  intros.
  simpl.
  lia.
Qed.

Lemma minus_zero_equiv: forall (a: expr_int),
  [[a - 0]] ~=~ a.
Proof.
  intros.
  unfold iequiv.
  intros.
  simpl.
  lia.
Qed.

Lemma zero_mult_equiv: forall (a: expr_int),
  [[0 * a]] ~=~ 0.
Proof.
  intros.
  unfold iequiv.
  intros.
  simpl.
  lia.
Qed.

Lemma mult_zero_equiv: forall (a: expr_int),
  [[a * 0]] ~=~ 0.
Proof.
  intros.
  unfold iequiv.
  intros.
  simpl.
  lia.
Qed.

Lemma const_plus_const: forall n m: Z,
  [[EConst n + EConst m]] ~=~ EConst (n + m).
Proof.
  intros.
  unfold iequiv.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma const_minus_const: forall n m: Z,
  [[EConst n - EConst m]] ~=~ EConst (n - m).
Proof.
  intros.
  unfold iequiv.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma const_mult_const: forall n m: Z,
  [[EConst n * EConst m]] ~=~ EConst (n * m).
Proof.
  intros.
  unfold iequiv.
  intros.
  simpl.
  reflexivity.
Qed.

(************)
(** 习题：  *)
(************)

(** 请证明下面SimpleWhile中整数类型表达式的行为等价。*)

Lemma plus_plus_assoc:
  forall a b c: expr_int,
    [[ a + (b + c) ]] ~=~ [[ a + b + c ]].
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Lemma plus_minus_assoc:
  forall a b c: expr_int,
    [[ a + (b - c) ]] ~=~ [[ a + b - c ]].
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Lemma minus_plus_assoc:
  forall a b c: expr_int,
    [[ a - (b + c) ]] ~=~ [[ a - b - c ]].
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Lemma minus_minus_assoc:
  forall a b c: expr_int,
    [[ a - (b - c) ]] ~=~ [[ a - b + c ]].
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


End DntSem_SimpleWhile1.

(** * Coq代数结构：等价关系 *)


(** 先前我们利用Coq归纳类型与递归函数定义了二叉树_[tree]_与二叉树结构相等
    _[same_structure]_。我们还证明过，_[same_structure]_具有传递性
    （_[same_structure_trans]_），事实上，我们还知道_[same_structure]_是一个等价关
    系！数学上，一个二元关系“≡”是一个等价关系当且仅当它满足下面三个性质：

        (1) 自反性：_[forall a, a ≡ a]_ 

        (2) 对称性：_[forall a b, a ≡ b -> b ≡ a]_ 

        (3) 传递性：_[forall a b c, a ≡ b -> b ≡ c -> a ≡ c]_ *)


Lemma same_structure_refl: forall t: tree,
  same_structure t t.
Proof.
  intros.
  induction t; simpl.
  + tauto.
  + tauto.
Qed.

Lemma same_structure_symm: forall t1 t2: tree,
  same_structure t1 t2 -> same_structure t2 t1.
Proof.
  intros.
  revert t2 H; induction t1; simpl; intros.
  + destruct t2; simpl.
    - tauto.
    - tauto.
  + destruct t2; simpl.
    - tauto.
    - specialize (IHt1_1 t2_1).
      specialize (IHt1_2 t2_2).
      tauto.
Qed.

(** 基于等价关系，我们可以对等价的元素进行替换。 *)

Example same_structure_ex1: forall t1 t2 t3 t4,
  same_structure t1 t2 ->
  same_structure t3 t2 ->
  same_structure t3 t4 ->
  same_structure t1 t4.

(** 它的Coq证明如下：*)

Proof.
  intros t1 t2 t3 t4 H12 H32 H34.
  apply (same_structure_trans t1 t2 t4).
  + apply H12.
  + apply (same_structure_trans t2 t3 t4).
    - apply same_structure_symm.
      apply H32.
    - apply H34.
Qed.

(** 在上面的这段Coq证明中，使用了_[same_structure]_的对称性和传递性。然而，更直观的证
    明思路也许应当用_[rewrite]_来刻画。例如，当我们证明整数相等的类似性质时，我们可以
    下面这样写证明。*)

Example Zeq_ex: forall x1 x2 x3 x4: Z,
  x1 = x2 ->
  x3 = x2 ->
  x3 = x4 ->
  x1 = x4.
Proof.
  intros x1 x2 x3 x4 H12 H32 H34.
  rewrite H12, <- H32, H34.
  reflexivity.
Qed.

(** Coq标准库提供了自反、对称、传递与等价的统一定义，并基于这些统一定义提供了
    _[rewrite]_、_[reflexivity]_等证明指令支持。下面三条证明中，_[Reflexive]_、
    _[Symmetric]_与_[Transitive]_是Coq标准库对于自反、对称与传递的定义。Coq标准库还
    将这三个定义注册成了Coq的Class，这使得Coq能够提供一些特定的证明支持。这里的关键字
    也不再使用_[Lemma]_或_[Theorem]_，而是使用_[Instance]_，这表示Coq将在后续证明过
    程中为_[same_structure]_提供自反、对称与传递相关的专门支持。*)

#[export] Instance same_structure_refl': Reflexive same_structure.
Proof. unfold Reflexive. apply same_structure_refl. Qed.

#[export] Instance same_structure_symm': Symmetric same_structure.
Proof. unfold Symmetric. apply same_structure_symm. Qed.

#[export] Instance same_structure_trans': Transitive same_structure.
Proof. unfold Transitive. apply same_structure_trans. Qed.

(** Coq还将这三条性质打包起来，定义了等价关系_[Equivalence]_。要在Coq中证明
    _[same_structure]_是一个等价关系，可以使用_[split]_指令，将“等价关系”规约为“自反
    性”、“对称性”与“传递性”。*)

#[export] Instance same_structure_equiv: Equivalence same_structure.
Proof.
  split.
  + apply same_structure_refl'.
  + apply same_structure_symm'.
  + apply same_structure_trans'.
Qed.

(** 现在，我们可以用_[rewrite]_与_[reflexivity]_重新证明上面的性质：*)

Example same_structure_ex2: forall t1 t2 t3 t4,
  same_structure t1 t2 ->
  same_structure t3 t2 ->
  same_structure t3 t4 ->
  same_structure t1 t4.
Proof.
  intros t1 t2 t3 t4 H12 H32 H34.
  rewrite H12, <- H32, H34.
  reflexivity.
Qed.



(** * Coq代数结构：Morphism *)

(** 尽管_[same_structure]_与普通的等号具有很多相似的性质，但是Coq现在并不支持我们能够
    像处理等号那样使用_[rewrite]_做替换。例如：*)

Example tree_reverse_same_structure_congr_ind_step:
  forall t11 t12 t21 t22 n1 n2,
    same_structure (tree_reverse t11) (tree_reverse t21) ->
    same_structure (tree_reverse t12) (tree_reverse t22) ->
    same_structure
      (Node (tree_reverse t11) n1 (tree_reverse t12))
      (Node (tree_reverse t21) n2 (tree_reverse t22)).
Proof.
  intros.
  Fail rewrite H, H0.
Abort.

(** 下面是_[same_structure]_与等号_[=]_的对比：*)

Example same_structure_vs_eq:
  forall t11 t12 t21 t22 n,
    tree_reverse t11 = tree_reverse t21 ->
    tree_reverse t12 = tree_reverse t22 ->
    Node (tree_reverse t11) n (tree_reverse t12) =
    Node (tree_reverse t21) n (tree_reverse t22).
Proof.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

(** Coq标准库提供了_[Proper]_表示“保持等价性”。*)

Definition any {A: Type} (a b: A): Prop := True.

#[export] Instance Node_same_structure_morphism:
  Proper (same_structure ==>
          any ==>
          same_structure ==>
          same_structure) Node.

(** 这个性质说得是：_[Node]_是一个三元函数，如果对其第一个参数做_[same_structure]_
    变换，对其第二个参数做任意变换，同时对其第三个参数做_[same_structure]_变换，那么
    这个三元函数的计算结果也会做_[same_structure]_变换。在证明这一结论时，需要展开
    _[Proper]_的定义，还需要展开_[==>]_的定义，它的Coq名字是_[respectful]_。*)

Proof.
  intros.
  unfold Proper, respectful.
  intros t11 t21 ? n1 n2 _ t12 t22 ?.
  simpl.
  tauto.
Qed.

(** 下面补充证明，_[any]_是一个自反关系。*)

#[export] Instance any_refl: forall A: Type, Reflexive (@any A).
Proof.
  intros.
  unfold Reflexive; intros.
  unfold any; tauto.
Qed.

(** 这样我们就可以让_[rewrite]_用上_[Node]_保持_[same_structure]_变换这一性质了。*)

Example tree_reverse_same_structure_congr_ind_step:
  forall t11 t12 t21 t22 n1 n2,
    same_structure (tree_reverse t11) (tree_reverse t21) ->
    same_structure (tree_reverse t12) (tree_reverse t22) ->
    same_structure
      (Node (tree_reverse t11) n1 (tree_reverse t12))
      (Node (tree_reverse t21) n2 (tree_reverse t22)).
Proof.
  intros.
  rewrite H, H0.
  simpl; split; reflexivity.
Qed.

(** 自然，_[tree_reverse]_保持_[same_structure]_也可以用_[Proper]_刻画。*)

#[export] Instance tree_reverse_same_structure_morphism:
  Proper (same_structure ==> same_structure) tree_reverse.
Proof.
  unfold Proper, respectful.
  intros t1.
  induction t1 as [| t11 IHt11 ? t12 IHt12]; intros t2 H;
    destruct t2 as [| t21 ? t22].
  + reflexivity.
  + simpl in H. tauto.
  + simpl in H. tauto.
  + simpl tree_reverse.
    simpl in H. destruct H as [Ht11 Ht12].
    specialize (IHt11 _ Ht11).
    specialize (IHt12 _ Ht12).
    rewrite IHt11, IHt12.
    simpl; split; reflexivity.
Qed.

(** 上面的例子中用_[Proper]_描述了_[Node]_与_[tree_reverse]_这两个函数的性质。其实
    _[Proper]_也可以用于描述谓词的性质。例如，下面性质说的是，如果对
    _[same_structure]_这个谓词的两个参数分别做_[same_structure]_变换，那么变换前后
    的两个命题要么全都成立要么全都不成立，即变换之前的命题成立当且仅当变换之后的命题成
    立，这个“当且仅当”就是下面定理描述中的_[iff]_。 *)

#[export] Instance same_structure_same_structure_morphism:
  Proper (same_structure ==> same_structure ==> iff) same_structure.
Proof.
  unfold Proper, respectful.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.


(** * 行为等价的性质 *)

Module DntSem_SimpleWhile1_Properties.
Import Lang_SimpleWhile
       StateModel_SimpleWhile1
       DntSem_SimpleWhile1.

(** 整数类型表达式之间的行为等价符合下面几条重要的代数性质。*)

#[export] Instance iequiv_refl: Reflexive iequiv.
Proof.
  unfold Reflexive, iequiv.
  intros.
  reflexivity.
Qed.

#[export] Instance iequiv_symm: Symmetric iequiv.
Proof.
  unfold Symmetric, iequiv.
  intros.
  rewrite H.
  reflexivity.
Qed.

#[export] Instance iequiv_trans: Transitive iequiv.
Proof.
  unfold Transitive, iequiv.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

#[export] Instance iequiv_equiv: Equivalence iequiv.
Proof.
  split.
  + apply iequiv_refl.
  + apply iequiv_symm.
  + apply iequiv_trans.
Qed.

#[export] Instance EAdd_iequiv_morphism:
  Proper (iequiv ==> iequiv ==> iequiv) EAdd.
Proof.
  unfold Proper, respectful, iequiv.
  intros.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

#[export] Instance ESub_iequiv_morphism:
  Proper (iequiv ==> iequiv ==> iequiv) ESub.
Proof.
  unfold Proper, respectful, iequiv.
  intros.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

#[export] Instance EMul_iequiv_morphism:
  Proper (iequiv ==> iequiv ==> iequiv) EMul.
Proof.
  unfold Proper, respectful, iequiv.
  intros.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

(** 利用这些代数性质，我们可以重新证明证明以下命题。*)

Fact iequiv_ex0:
  forall (a: expr_int) (n m: Z),
    [[ a + (EConst n) + (EConst m) ]] ~=~
    EAdd a (EConst (n + m)).
Proof.
  intros.
  rewrite <- plus_plus_assoc.
  rewrite const_plus_const.
  reflexivity.
Qed.


End DntSem_SimpleWhile1_Properties.

(** * 函数与等价关系 *)

Module PointwiseRelDemo.

(** 对于类型_[B]_上的二元关系_[R]_，可以定义二元关系_[pointwise_relation A R]_：*)

Definition pointwise_relation
             (A: Type) {B: Type}
             (R: B -> B -> Prop)
             (f g: A -> B): Prop :=
  forall a: A, R (f a) (g a).

(** Coq标准库也证明了，如果_[R]_是等价关系，那么_[pointwise_relation A R]_也是等价关
    系。*)

#[export] Instance pointwise_reflexive:
  forall {A B: Type} {R: B -> B -> Prop},
    Reflexive R ->
    Reflexive (pointwise_relation A R).
Proof.
  intros.
  unfold Reflexive, pointwise_relation.
  (** 展开定义后需要证明
      - _[forall (x: A -> B) a, R (x a) (x a)]_。*)
  intros.
  reflexivity.
  (** 这一步是使用二元关系_[R]_的自反性完成证明。*)
Qed.

#[export] Instance pointwise_symmetric:
  forall {A B: Type} {R: B -> B -> Prop},
    Symmetric R ->
    Symmetric (pointwise_relation A R).
Proof.
  intros.
  unfold Symmetric, pointwise_relation.
  intros.
  (** 展开定义后需要证明的前提和结论是：
      - H0: forall a, R (x a) (y a)
      - 结论: R (y a) (x a) *)
  symmetry.
  (** 这里的_[symmetry]_指令表示使用对称性。*)
  apply H0.
Qed.

#[export] Instance pointwise_transitive:
  forall {A B: Type} {R: B -> B -> Prop},
    Transitive R ->
    Transitive (pointwise_relation A R).
Proof.
  intros.
  unfold Transitive, pointwise_relation.
  intros.
  (** 展开定义后需要证明的前提和结论是：
      - H0: forall a, R (x a) (y a)
      - H1: forall a, R (y a) (z a)
      - 结论: R (x a) (z a) *)
  transitivity (y a).
  (** 这里，_[transitivity (y a)]_表示用“传递性”证明并选_[y a]_作为中间元素。*)
  + apply H0.
  + apply H1.
Qed.

#[export] Instance pointwise_equivalence:
  forall {A B: Type} {R: B -> B -> Prop},
    Equivalence R ->
    Equivalence (pointwise_relation A R).
Proof.
  intros.
  split.
  + apply pointwise_reflexive.
    apply Equivalence_Reflexive.
  + apply pointwise_symmetric.
    apply Equivalence_Symmetric.
  + apply pointwise_transitive.
    apply Equivalence_Transitive.
Qed.

End PointwiseRelDemo.

(** 在Coq中，普通的等号_[=]_实际是一个Notation，其背后的定义名称为_[eq]_。这是一个多
    态二元谓词，例如_[@eq Z]_表示“整数相等”，_[@eq (list Z)]_表示“整数列表相等”。这
    个等号表示的“相等”自然也是一个等价关系，这一定理在Coq标准库中的描述如下：
   
      eq_equivalence: forall {A : Type}, Equivalence (@eq A)
      
    更进一步，两个类型为_[A -> B]_的函数，“它们在_[A]_类型的自变量任意取值时求值结果
    都相同”就可以用下面二元关系表示：*)
Definition func_equiv (A B: Type):
  (A -> B) -> (A -> B) -> Prop :=
  pointwise_relation A (@eq B).

(** 我们在Coq中用_[==]_表示函数相等，为了区别于其它使用_[==]_的情况，我们在用
    _[%func]_环境专指表示函数相等。*)

Declare Scope func_scope.
Delimit Scope func_scope with func.
Notation "f == g" :=
  (func_equiv _ _ f g)
  (at level 70, no associativity): func_scope.

(** 我们知道，_[func_equiv]_也一定是一个等价关系。*)

#[export] Instance func_equiv_equiv:
  forall A B, Equivalence (func_equiv A B).
Proof.
  intros.
  apply pointwise_equivalence.
  apply eq_equivalence.
Qed.

(** 除了可以定义函数之间的等价关系之外，还可以反过来利用函数构造等价关系。*)

Theorem equiv_in_domain:
  forall {A B: Type} (f: A -> B) (R: B -> B -> Prop),
    Equivalence R ->
    Equivalence (fun a1 a2 => R (f a1) (f a2)).
Proof.
  intros.
  split.
  + unfold Reflexive.
    intros.
    reflexivity.
  + unfold Symmetric.
    intros.
    symmetry; tauto.
  + unfold Transitive.
    intros.
    transitivity (f y); tauto.
Qed.

(** * 利用高阶函数定义指称语义 *)

Module DntSem_SimpleWhile2.
Import Lang_SimpleWhile
       StateModel_SimpleWhile1.

(** * 扩展状态表示 *)
Record io_state := {
  vars: var_name -> Z;  (* 变量的值 *)
  input_queue: list Z;  (* 输入队列 *)
  output_queue: list Z  (* 输出队列 *)
}.

(** * 表达式语义（整数和布尔） *)
Definition add_sem (D1 D2: io_state -> Z) (s: io_state): Z := D1 s + D2 s.
Definition sub_sem (D1 D2: io_state -> Z) (s: io_state): Z := D1 s - D2 s.
Definition mul_sem (D1 D2: io_state -> Z) (s: io_state): Z := D1 s * D2 s.

Definition const_sem (n: Z): io_state -> Z := fun s => n.
Definition var_sem (X: var_name): io_state -> Z := fun s => s.(vars) X.

Fixpoint eval_expr_int (e: expr_int): io_state -> Z :=
  match e with
  | EConst n => const_sem n
  | EVar X => var_sem X
  | EAdd e1 e2 => add_sem (eval_expr_int e1) (eval_expr_int e2)
  | ESub e1 e2 => sub_sem (eval_expr_int e1) (eval_expr_int e2)
  | EMul e1 e2 => mul_sem (eval_expr_int e1) (eval_expr_int e2)
  end.

Definition true_sem: io_state -> bool := fun s => true.
Definition false_sem: io_state -> bool := fun s => false.
Definition lt_sem (D1 D2: io_state -> Z): io_state -> bool :=
  fun s => if Z_lt_dec (D1 s) (D2 s) then true else false.
Definition and_sem (D1 D2: io_state -> bool): io_state -> bool :=
  fun s => andb (D1 s) (D2 s).
Definition not_sem (D: io_state -> bool): io_state -> bool :=
  fun s => negb (D s).

Fixpoint eval_expr_bool (e: expr_bool): io_state -> bool :=
  match e with
  | ETrue => true_sem
  | EFalse => false_sem
  | ELt e1 e2 => lt_sem (eval_expr_int e1) (eval_expr_int e2)
  | EAnd e1 e2 => and_sem (eval_expr_bool e1) (eval_expr_bool e2)
  | ENot e1 => not_sem (eval_expr_bool e1)
  end.

(** * 命令语法扩展 *)
Inductive stmt :=
  | SSkip
  | SAssign (X: var_name) (e: expr_int)
  | SSeq (s1 s2: stmt)
  | SIf (e: expr_bool) (s1 s2: stmt)
  | SWhile (e: expr_bool) (s: stmt)
  | SRead (X: var_name)       (* 新增语法：读操作 *)
  | SWrite (e: expr_int).     (* 新增语法：写操作 *)

(** * 新语义算子：IO操作 *)
Definition read_sem (X: var_name) (s: io_state): io_state :=
  match s.(input_queue) with
  | [] => s (* 若输入队列为空，状态保持不变 *)
  | v :: vs =>
      {| vars := fun Y => if eqb Y X then v else s.(vars) Y;
         input_queue := vs;
         output_queue := s.(output_queue) |}
  end.

Definition write_sem (e: io_state -> Z) (s: io_state): io_state :=
  {| vars := s.(vars);
     input_queue := s.(input_queue);
     output_queue := s.(output_queue) ++ [e s] |}.

(** * 命令的语义 *)
Fixpoint eval_stmt (st: stmt) (s: io_state): io_state :=
  match st with
  | SSkip => s
  | SAssign X e =>
      {| vars := fun Y => if eqb Y X then ⟦ e ⟧ s else s.(vars) Y;
         input_queue := s.(input_queue);
         output_queue := s.(output_queue) |}
  | SSeq s1 s2 =>
      let s' := eval_stmt s1 s in
      eval_stmt s2 s'
  | SIf e s1 s2 =>
      if ⟦ e ⟧ s then eval_stmt s1 s else eval_stmt s2 s
  | SWhile e body =>
      if ⟦ e ⟧ s then eval_stmt (SSeq body (SWhile e body)) s else s
  | SRead X => read_sem X s
  | SWrite e => write_sem ⟦ e ⟧ s
  end.

(** * 测试实例 *)
Example test_io:
  let s := {| vars := fun _ => 0; input_queue := [42; 7]; output_queue := [] |} in
  let prog := SSeq (SRead "x")
                   (SSeq (SWrite ("x" + 1))
                         (SWrite ("x" * 2))) in
  eval_stmt prog s =
  {| vars := fun Y => if eqb Y "x" then 42 else 0;
     input_queue := [7];
     output_queue := [43; 84] |}.
Proof.
  simpl. reflexivity.
Qed.

End DntSem_SimpleWhile2.

