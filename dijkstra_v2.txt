
Require Import List.
Import ListNotations.
Require Import Lia.
Require Import Program.Equality.
Require Import Arith.PeanoNat.
Require Import Recdef.
Require Import Arith.Compare_dec.



(* I) graphs and path *)

Definition Graph := list (list (nat * nat)).
(* adjency list: we have couples: (taget_nod_id, weigth) *)

Definition consistent_weigth (G : Graph) : Prop :=
    forall (i j w w':nat), In (j,w) (nth i G []) -> In (j,w') (nth i G []) -> w = w'.
(* checks the weigth are consistent ;) *)

Definition is_graph (G : Graph) : Prop :=
  consistent_weigth G /\
  forall i l, nth_error G i = Some l -> (* "l = G[i]" *)
    forall (j w:nat), In (j,w) l -> j < length G.
(* checks the node's ids appearing in G are legal *)

Definition vertex_is_in (G : Graph) (u: nat) : Prop :=
  u < length G.
(* checks that the vertex u is in G *)

Definition Path := list nat.
(* list of vertex *)

Inductive is_path (G : Graph) : Path -> Type :=
| path_single i : vertex_is_in G i -> is_path G [i]
| path_cons i j rest w :
    vertex_is_in G i ->
    In (j,w) (nth i G []) ->
    is_path G (j :: rest) ->
    is_path G (i :: j :: rest).

Fixpoint path_weight (G : Graph) (p : Path) (H : is_path G p) : nat :=
  match H with
  | path_single _ _ _ => 0
  | path_cons _ i_ j rest w _ Hin Hrest =>
      w + path_weight G (j :: rest) Hrest
  end.

(* equivalent definitions *)

Fixpoint is_path' (G : Graph) (p : Path) : Prop :=
  match p with
  | [] => False
  | [u] => vertex_is_in G u
  | i :: ((j :: _) as rest) =>
      vertex_is_in G i /\ (exists w, In (j,w) (nth i G [])) /\ is_path' G rest
  end.

Fixpoint last {A} (l : list A) (d : A) : A :=
  match l with
  | [] => d
  | [x] => x
  | _ :: xs => last xs d
  end.
Definition is_path_from_to (G : Graph) (p : Path) (u v: nat) : Prop :=
  match p with
  | [] => False
  | [i] => vertex_is_in G i /\ i=u /\ i=v
  | i :: _ =>
      is_path' G p /\ i=u /\ last p (length G) = v (*length G : plus grand que tout les sommets : id inatteignable*)
  end.

Lemma is_path_from_to_IS_A_PATH G p u v: is_path_from_to G p u v -> is_path' G p.
Proof. destruct p as [| i [| j p]]; simpl; tauto. Qed.

Fixpoint path_weight' (G : Graph) (p : Path) : option nat :=
  match p with
  | [] => None
  | [_] => Some 0
  | i :: ((j :: _) as rest) =>
      match find (fun '(k,w) => Nat.eqb k j) (nth i G []) with
      | Some (_,w) =>
          match path_weight' G rest with
          | Some w' => Some (w + w')
          | None => None
          end
      | None => None
      end
  end.

(* auxilary tools about find *)

Lemma find_spec :
  forall (A : Type) (f : A -> bool) (l : list A),
    (exists (x : A), find f l = Some x) <-> (exists x:A, In x l /\ f x = true).
Proof.
  split.
  - intro. destruct H. exists x. apply (find_some f l H).
  - induction l; simpl; intro; destruct H; try tauto.
    destruct (f a) eqn:Fa.
    + exists a. reflexivity.
    + destruct H as [[H|H] H0].
      * rewrite H in Fa. rewrite Fa in H0. discriminate.
      * apply IHl. exists x. tauto.
Qed.

Lemma find_prop :
  forall (A : Type) (f : A -> bool) (l : list A),
    (exists (x : A), find f l = Some x) -> (exists x:A, In x l /\ f x = true /\ find f l = Some x).
Proof. intros. destruct H. pose proof H. apply find_some in H0. exists x. tauto. Qed.

Lemma find_In_eq :
  forall (l:list (nat*nat)) n w
    (H_consistent: forall (j w w':nat), In (j,w) l -> In (j,w') l -> w = w'),
    In (n,w) l ->
    find (fun '(k,_) => Nat.eqb k n) l = Some (n,w).
Proof.
  intros.
  pose proof (find_prop _ (fun '(k, _) => k =? n) l).
  destruct (find_spec _ (fun '(k, _) => k =? n) l) as [_ H1].
  specialize (H1 ltac:(exists (n, w); split; try assumption; exact (Nat.eqb_refl n))).
  specialize (H0 H1). destruct H0 as [x [H0 [H2 H3]]]. rewrite H3.
  destruct x as [n' w'].
  apply Nat.eqb_eq in H2. rewrite H2 in *.
  replace w with w' by exact (H_consistent _ _ _ H0 H).
  reflexivity.
Qed.

(*to go from Prop to Set*)
Lemma exists_to_sig :
  forall (G: Graph) a n
    (H_cons: consistent_weigth G),
    (exists w, In (n, w) (nth a G [])) ->
    { w | In (n, w) (nth a G []) }.
Proof.
  intros G a n H_cons H.
  destruct (find (fun '(k,_) => Nat.eqb k n) (nth a G [])) as [w|] eqn:E.
  - destruct w. exists n1.
    pose proof (find_prop _ (fun '(k, _) => k =? n) (nth a G [])).
    specialize (H0 ltac:(exists (n0, n1); exact E)). destruct H0 as [x [H0[H1 H2]]].
    rewrite E in H2. injection H2 as H3. rewrite <- H3 in *.
    simpl in H1. apply Nat.eqb_eq in H1. rewrite H1 in H0. exact H0.
  - exfalso. destruct H as [w HIn]. apply find_In_eq in HIn. 2:exact (H_cons a).
    rewrite HIn in E. discriminate E.
Qed.

(* proof equivalences *)

(*aux lemma*)
Lemma path_non_empty G p: is_path G p -> p <> [].
Proof. intro. destruct H; discriminate. Qed.

Lemma path_equiv_1 G p: is_path G p -> is_path' G p.
Proof.
  intro. induction p.
  - apply path_non_empty in H. contradiction.
  - destruct p.
    + simpl. inversion H. exact H1.
    + inversion H. repeat split.
      * assumption.
      * exists w. assumption.
      * apply IHp. assumption.
Qed.

Lemma path_equiv_2 G p (H_cons: consistent_weigth G): is_path' G p -> is_path G p.
Proof.
  intro. induction p.
  - simpl in H. contradiction.
  - destruct p.
    + apply (path_single _ a). assumption.
    + destruct H as [H[H0 H1]]. apply exists_to_sig in H0. 2:exact H_cons.
      destruct H0. apply (path_cons _ a n p x); tauto.
Qed.

Lemma path_weigth_equiv_1 G p (H_cons: consistent_weigth G) (H:is_path G p) (H':is_path G p): path_weight G p H = path_weight G p H'.
Proof.
  induction p. 
  1:pose proof (path_non_empty _ _ H); contradiction.
  dependent destruction H; dependent destruction H'; simpl.
  - reflexivity.
  - rewrite (IHp H H').
    replace w with w0. 2:exact (H_cons a _ _ _ i1 i0).
    reflexivity.
Qed.

Lemma path_weigth_equiv_2 G p (H_cons: consistent_weigth G) (H:is_path G p) : path_weight' G p = Some (path_weight G p H).
Proof.
  induction p.
  - pose proof (path_non_empty _ _ H). contradiction.
  - destruct p.
    + simpl. f_equal. dependent destruction H. simpl. reflexivity.
    + inversion H. specialize (IHp H5). dependent destruction H. simpl in *. rewrite IHp.
      rewrite (find_In_eq (nth a G []) _ _ (H_cons a) i0).
      rewrite (path_weigth_equiv_1 G (n::p) H_cons H5 H).
      reflexivity.
Qed.

(* path of minilam length *)

Definition minimum_path_from_to (G : Graph) (p : Path) (u v: nat) (H_cons: consistent_weigth G) (H_p: is_path_from_to G p u v) : Prop :=
  forall (p':Path) (H_p': is_path_from_to G p' u v),
  path_weight G p (path_equiv_2 _ _ H_cons (is_path_from_to_IS_A_PATH _ _ _ _ H_p))
  <= path_weight G p' (path_equiv_2 _ _ H_cons(is_path_from_to_IS_A_PATH _ _ _ _ H_p')).

(* chemin restreint à des sommets *)

Fixpoint is_path_restr (G : Graph) (p : Path) (pq: list nat): Prop :=
  (*pq : queue : on interdit de passer par les sommets de pq, sauf pour le dernier*)
  match p with
  | [] => False
  | [u] => vertex_is_in G u
  | i :: ((j :: _) as rest) =>
      ~(In i pq) /\ vertex_is_in G i /\ (exists w, In (j,w) (nth i G [])) /\ is_path_restr G rest pq
  end.

Lemma is_path_restr_IS_A_PATH G p pq: is_path_restr G p pq -> is_path' G p.
Proof. intro. induction p; try contradiction. destruct p as [| i [| j p]]; simpl in *; tauto. Qed.

Definition is_path_from_to_restr (G : Graph) (p : Path) (pq: list nat) (u v: nat) : Prop :=
  match p with
  | [] => False
  | [i] => vertex_is_in G i /\ i=u /\ i=v
  | i :: _ =>
      is_path_restr G p pq /\ i=u /\ last p (length G) = v (*length G : plus grand que tout les sommets : id inatteignable*)
  end.

Lemma is_path_from_to_restr_IS_A_PATH G p pq u v: is_path_from_to_restr G p pq u v -> is_path' G p.
Proof.
  intro. destruct p as [| i [| j p]]; simpl in *; try tauto.
  destruct p; repeat split; try tauto. apply (is_path_restr_IS_A_PATH _ _ pq). tauto.
Qed.

Lemma rest_is_not_restr G p pq src v0: is_path_from_to_restr G p pq src v0 -> is_path_from_to G p src v0.
Proof.
  intro. destruct p as [| i [| j p]]; simpl in *; try tauto.
  destruct p; repeat split; try tauto. apply (is_path_restr_IS_A_PATH _ _ pq). tauto.
Qed.

Definition minimum_path_from_to_restr (G : Graph) (p : Path) (pq: list nat) (u v: nat) (H_cons: consistent_weigth G) (H_p: is_path_from_to_restr G p pq u v) : Prop :=
  forall (p':Path) (H_p': is_path_from_to_restr G p' pq u v),
  path_weight G p (path_equiv_2 _ _ H_cons (is_path_from_to_restr_IS_A_PATH _ _ pq _ _ H_p))
  <= path_weight G p' (path_equiv_2 _ _ H_cons(is_path_from_to_restr_IS_A_PATH _ _ pq _ _ H_p')).

(* lemmas path *)

Lemma path_refl (G : Graph) (u: nat): vertex_is_in G u -> exists p, is_path_from_to G p u u.
Proof. intro. exists [u]. repeat split; try reflexivity. assumption. Qed.
Lemma path_edge (G : Graph) (u v: nat): (exists (w: nat), In (v, w) (nth u G [])) -> (vertex_is_in G u) -> (vertex_is_in G v) -> exists p, is_path_from_to G p u v.
Proof. intro. exists [u; v]. repeat split; try assumption. Qed.
Lemma last_in_G (G : Graph) (p: Path): is_path' G p -> vertex_is_in G (dijkstra_v2.last p (length G)).
Proof. intro. induction p; try contradiction. destruct p; simpl in *; try apply IHP; tauto. Qed.
Lemma ext_in_G (G : Graph) (p: Path) (u v: nat): is_path_from_to G p u v -> vertex_is_in G v /\ vertex_is_in G u.
Proof.
  intro. destruct p; try contradiction. destruct p.
  - destruct H as [H [H1 H2]]. rewrite <- H1. rewrite <- H2. tauto.
  - destruct H as [[H H'] [H1 H2]]. rewrite <- H1. split; try assumption.
    rewrite <- H2. apply last_in_G. split; tauto.
Qed.
Lemma path_cut (G : Graph) (p': Path) (u0 u1 u2 u3: nat): is_path_from_to G (u2::u3::p') u0 u1 -> is_path_from_to G (u2::u3::[]) u0 u3 /\ is_path_from_to G (u3::p') u3 u1.
Proof. intros. destruct H as [[H1 [H2 H3]] [H4 H5]]. split; destruct p'; simpl in *; tauto. Qed.
Lemma path_ext (G : Graph) (p: Path) (u u' v: nat): vertex_is_in G u -> is_path_from_to G p u' v -> (exists w, In (u', w) (nth u G [])) -> is_path_from_to G (u::p) u v.
Proof.
  intros. destruct p; try contradiction.
  repeat split; destruct p; try (simpl in *; tauto).
  all: destruct H0 as [_ [H0 _]]; rewrite H0; assumption.
Qed.
Lemma path_trans (G : Graph) (p p': Path) (u v w: nat): is_path_from_to G p u v -> is_path_from_to G (v::p') v w -> is_path_from_to G (p++p') u w.
Proof.
  revert u. induction p; try contradiction.
  intros. rewrite <- app_comm_cons in *. destruct p.
  + destruct H as [H[H1 H2]]. rewrite H1 in *. rewrite H2. assumption.
  + pose proof H as H1. destruct H as [[H [H2 _]] [H3 _]].
    rewrite H3 in *. apply path_cut in H1.
    apply (path_ext _ _ _ n _); try assumption.
    apply (IHp n); tauto.
Qed.
(*encore une fois tout le bazard du dessus aurait pu etre evité par une meilleure définition*)



(* II) Heap *)

(* dist *)

(* None = +∞, Some n = distance finie *)
Definition dist := list (option nat).

(* init_dist n src : distances pour 0..n-1, source à 0, le reste à +∞ *)
Fixpoint init_dist (n src : nat) : dist :=
  match n with
  | 0 => []
  | S n' =>
      if Nat.eqb src 0
      then Some 0 :: repeat None n'
      else None   :: init_dist n' (src - 1)
  end.

(* accès: si hors-borne -> +∞ *)
Definition get_dist (d : dist) (i : nat) : option nat :=
  nth i d None.

(* mise à jour (hors-borne: no-op) *)
Fixpoint update_dist (d : dist) (i : nat) (v : option nat) : dist :=
  match d, i with
  | [], _ => []
  | _ :: tl, 0 => v :: tl
  | hd :: tl, S k => hd :: update_dist tl k v
  end.

(* ordre: Some a <= Some b selon Nat.leb; Some _ < None; None = +∞ *)
Definition opt_le (x y : option nat) : bool :=
  match x, y with
  | None, None => true
  | Some _, None => true
  | None, Some _ => false
  | Some a, Some b => Nat.leb a b
  end.

Lemma opt_le_refl x: opt_le x x = true.
Proof. destruct x; try reflexivity. simpl. exact (Nat.leb_refl n). Qed.
Lemma opt_le_trans x y z: opt_le x y = true -> opt_le y z = true -> opt_le x z = true.
Proof.
  intros. destruct x, y, z; simpl in *; try tauto; try discriminate;
  apply Nat.leb_le in H, H0; apply Nat.leb_le; lia.
Qed.
Lemma opt_le_tot x y: opt_le x y = true \/ opt_le x y = false.
Proof.
  intros. destruct x, y; simpl in *; try tauto.
  destruct (n <=? n0); tauto.
Qed.
Lemma opt_le_tot' x y: opt_le x y = false -> opt_le y x = true.
Proof.
  intros. destruct x, y; simpl in *; try tauto; try discriminate.
  apply Compare_dec.leb_complete_conv in H. apply Nat.leb_le; lia.
Qed.

(* distance minimale *)

Definition minimum_dist_from_to (G : Graph) (d : option nat) (u v: nat) (H_cons: consistent_weigth G) : Prop :=
  (~(exists p, is_path_from_to G p u v) /\ d = None) \/
  (exists p, is_path_from_to G p u v /\ d = path_weight' G p /\
  forall (p':Path), is_path_from_to G p' u v -> opt_le d (path_weight' G p') = true).

Definition minimum_dist_from_to_is_restr (G : Graph) (d: option nat) (pq: list nat) (u v: nat) (H_cons: consistent_weigth G) : Prop :=
  (~(exists p, is_path_from_to G p u v) /\ d = None) \/
  (exists p, is_path_from_to_restr G p pq u v /\ d = path_weight' G p /\
  forall (p':Path), is_path_from_to G p' u v -> opt_le d (path_weight' G p') = true).

Definition minimum_dist_from_to_restr (G : Graph) (d: option nat) (pq: list nat) (u v: nat) (H_cons: consistent_weigth G) : Prop :=
  (~(exists p, is_path_from_to_restr G p pq u v) /\ d = None) \/
  (exists p, is_path_from_to_restr G p pq u v /\ d = path_weight' G p /\
  forall (p':Path), is_path_from_to_restr G p' pq u v -> opt_le d (path_weight' G p') = true).

(* heap *)

Definition pqueue := list nat.

(* sommets 0..n-1 *)
Fixpoint init_pq (n : nat) : pqueue :=
  match n with
  | 0 => []
  | S k => k :: init_pq k
  end.

Fixpoint in_pq (x : nat) (pq : pqueue) : bool :=
  match pq with
  | [] => false
  | y :: tl => if Nat.eqb x y then true else in_pq x tl
  end.

Lemma remove_decreases : forall x pq,
  In x pq -> length (remove Nat.eq_dec x pq) < length pq.
Proof. intros. apply remove_length_lt. assumption. Qed.

(* comparer deux sommets via leurs distances *)
Definition le_by_dist (d : dist) (u v : nat) : bool :=
  opt_le (get_dist d u) (get_dist d v).

(* trouve l’argmin dans une liste non vide *)
Fixpoint argmin_nonempty (d : dist) (x : nat) (xs : pqueue) : nat :=
  match xs with
  | [] => x
  | y :: ys =>
      if le_by_dist d x y
      then argmin_nonempty d x ys
      else argmin_nonempty d y ys
  end.

Lemma argmin_nonempty_correct d n pq: In (argmin_nonempty d n pq) (n :: pq).
Proof.
  revert n. induction pq; intro; simpl; try tauto.
  destruct (le_by_dist d n a).
  1: specialize (IHpq n). 2: specialize (IHpq a).
  all: destruct IHpq; tauto.
Qed.

Lemma argmin_nonempty_min d l : forall x n pq, length pq = l -> In x (n::pq) -> (le_by_dist d (argmin_nonempty d n pq) x)=true.
Proof.
  induction l; intros.
  - apply length_zero_iff_nil in H. rewrite H in *.
    simpl in *. destruct H0; try contradiction.
    rewrite H0. unfold le_by_dist. apply opt_le_refl.
  - destruct pq.
    + simpl in H. lia.
    + destruct H0 as [H0 | [H0 | H0]]; simpl; destruct (le_by_dist d n n0) eqn:Hn; try (rewrite <- H0 in *);
        try (apply IHl; simpl in *; try lia; tauto); (* 4 simple cases *)
        pose proof (argmin_nonempty_correct d n0 pq).
      * pose proof (IHl n0 n0 pq ltac:(simpl in H; lia) ltac:(simpl; tauto)).
        apply opt_le_tot' in Hn.
        apply (opt_le_trans _ (get_dist d n0) _); assumption.
      * pose proof (IHl n n pq ltac:(simpl in H; lia) ltac:(simpl; tauto)).
        apply (opt_le_trans _ (get_dist d n) _); assumption.
Qed.

Lemma argmin_nonempty_first_min d a pq: (forall x, In x pq -> (le_by_dist d a x)=true) -> argmin_nonempty d a pq = a.
Proof.
  induction pq; try reflexivity.
  intro. simpl. rewrite (H a0 ltac:(simpl; tauto)). apply IHpq.
  intros. apply H. simpl. right. exact H0.
Qed.

(* extraction du min; None si file vide *)
Definition extract_min (pq : pqueue) (d : dist) : option (nat * pqueue) :=
  match pq with
  | [] => None
  | x :: xs =>
      let m := argmin_nonempty d x xs in
      Some (m, remove Nat.eq_dec m pq)
  end.

Lemma extract_min_empty_aux0 d l: forall a n pq, length pq = l -> argmin_nonempty d a (n::pq) = a \/ argmin_nonempty d a (n::pq) = (argmin_nonempty d n pq).
Proof.
  induction l.
  - intros. simpl. apply length_zero_iff_nil in H. rewrite H.
    destruct (le_by_dist d a n); tauto.
  - intros. simpl. destruct (le_by_dist d a n) eqn:H0; try tauto.
    destruct pq.
    + simpl. tauto.
    + simpl in H. pose proof (IHl a n0 pq ltac:(lia)). specialize (IHl n n0 pq ltac:(lia)). destruct IHl; destruct H1; try tauto.
      * left. apply argmin_nonempty_first_min. intros.
        pose proof (argmin_nonempty_min d (length (n0::pq)) x n (n0::pq) ltac:(reflexivity) ltac:(simpl; tauto)).
        rewrite H2 in H4. apply (opt_le_trans _ (get_dist d n) _); assumption.
        (*a <= n <= n0::pq : a est au debut et est petit : c'est le min*)
      * right. lia.
Qed.

Lemma extract_min_empty pq d: pq <> [] <-> exists u pq', extract_min pq d = Some(u, pq').
Proof.
  split; intro.
  - induction pq; try contradiction. destruct pq.
    + exists a, []. simpl. destruct (Nat.eq_dec a a); tauto.
    + destruct (argmin_nonempty d a (n :: pq) =? a) eqn:H0.
      * exists a, (remove Nat.eq_dec a (n::pq)). unfold extract_min.
        apply Nat.eqb_eq in H0. rewrite H0. simpl. destruct (Nat.eq_dec a a); tauto.
      * specialize (IHpq ltac:(discriminate)). destruct IHpq as [u [pq' H1]].
        assert (argmin_nonempty d a (n :: pq) = u).
        {
          inversion H1. apply Nat.eqb_neq in H0.
          destruct (extract_min_empty_aux0 d (length pq) a n pq ltac:(reflexivity)).
          contradiction. assumption.
        }
        destruct (u =? n) eqn:H3.
        1: exists u, (a::remove Nat.eq_dec u pq). 2: exists u, (a :: n :: remove Nat.eq_dec u pq).
        all: unfold extract_min; apply Nat.eqb_neq in H0; rewrite H2; simpl;
          rewrite H2 in H0; apply Nat.eqb_neq in H0; destruct (Nat.eq_dec u a); try (rewrite e, Nat.eqb_refl in H0; discriminate); destruct (Nat.eq_dec u n); try (apply Nat.eqb_eq in H3; lia); try (apply Nat.eqb_neq in H3; lia); reflexivity.
  - intro. rewrite H0 in H. destruct H as [u [pq'H]]. unfold extract_min in H. discriminate.
Qed.

Lemma remove_removes_all d pq pq' u: extract_min pq d = Some (u, pq') -> ~ In u pq'.
Proof.
  intro. unfold extract_min in H. destruct pq; try discriminate.
  inversion H. destruct (Nat.eq_dec (argmin_nonempty d n pq) n); try apply remove_In.
  simpl. intro. destruct H0; try lia.
  absurd (In (argmin_nonempty d n pq) (remove Nat.eq_dec (argmin_nonempty d n pq) pq)); try assumption. apply remove_In.
Qed.

Lemma remove_decrease' u0 u1 l: In u0 (remove Nat.eq_dec u1 l) -> In u0 l.
Proof.
  intro. induction l.
  - simpl in H. contradiction.
  - simpl in H. destruct (Nat.eq_dec  u1 a); simpl in *; tauto.
Qed.

Lemma not_in_pq'_aux u0 u1 l: In u0 l -> ~(In u0 (remove Nat.eq_dec u1 l)) -> u0 = u1.
Proof.
  intros. destruct (Nat.eq_dec u0 u1); try assumption.
  apply (in_in_remove Nat.eq_dec _ n) in H. contradiction.
Qed.

Lemma not_in_pq' pq pq' d u u1: extract_min pq d = Some (u, pq') -> ~ In u1 pq' -> u1 = u \/ ~ In u1 pq.
Proof.
  intros. destruct (In_dec Nat.eq_dec u1 pq); try tauto.
  left. destruct pq; simpl in H; try discriminate.
    simpl in H0. inversion H. rewrite H2 in *.
    destruct (u=?n) eqn:Hdisj.
    + apply Nat.eqb_eq in Hdisj. destruct i; try lia. 
      destruct (Nat.eq_dec u n); try contradiction.
      apply (not_in_pq'_aux _ _ pq); try assumption.
      rewrite H3. assumption.
    + apply Nat.eqb_neq in Hdisj.
      destruct (Nat.eq_dec u n); try contradiction.
      rewrite <- H3 in H0. simpl in H0.
      assert ((n <> u1 /\ ~ In u1 (remove Nat.eq_dec u pq))) by tauto.
      destruct H1. destruct i; try contradiction.
      apply (not_in_pq'_aux _ _ _ H5 H4).
Qed.

Lemma dist_u_min_in_d pq pq' d u u':
  extract_min pq d = Some (u, pq') -> In u' pq' -> le_by_dist d u u' = true.
Proof.
  intros. induction pq; try discriminate.
  pose proof (argmin_nonempty_min d (length pq) u' a pq ltac:(reflexivity)).
  inversion H. rewrite H3 in *. apply H1.
  destruct (u =? a); rewrite <- H4 in H0.
  all: pose proof (remove_decrease' u' u pq).
  all: destruct (Nat.eq_dec u a); simpl in *; tauto.
Qed.

Lemma dist_u_min_in_d_ pq pq' d u u':
  extract_min pq d = Some (u, pq') -> In u' pq -> le_by_dist d u u' = true.
Proof.
  intros. induction pq; try discriminate.
  pose proof (argmin_nonempty_min d (length pq) u' a pq ltac:(reflexivity)).
  inversion H. rewrite H3 in *. apply H1. assumption.
Qed.

Lemma pq'_inc_pq d pq pq' u u0: extract_min pq d = Some (u, pq') -> In u0 pq' -> In u0 pq.
Proof.
  intros. unfold extract_min in H. destruct pq; try discriminate. inversion H. simpl.
  destruct (Nat.eq_dec (argmin_nonempty d n pq) n).
  - right. rewrite <- H3 in H0. apply remove_decrease' in H0. assumption.
  - rewrite <- H3 in H0. destruct H0; try tauto. right. apply remove_decrease' in H0. assumption.
Qed.




(* III) Dijkstra *)

(* relaxation arrète *)

(* addition sécurisée pour option nat *)
Definition opt_add (a b : option nat) : option nat :=
  match a, b with
  | Some x, Some y => Some (x + y)
  | _, _ => None
  end.

(* test strict: x < y en tenant compte de +∞ *)
Definition opt_lt (x y : option nat) : bool :=
  match x, y with
  | None, _ => false          (* +∞ n'est jamais < *)
  | Some _, None => true      (* fini < +∞ *)
  | Some a, Some b => Nat.ltb a b
  end.
Lemma rel_opt_le_lt x y: opt_le x y = true <-> opt_lt y x = false.
Proof.
  split.
  - intro. destruct x, y; simpl in *; try tauto; try discriminate.
    apply Nat.ltb_ge. apply Nat.leb_le. assumption.
  - intro. destruct x, y; simpl in *; try tauto; try discriminate.
    apply Nat.ltb_ge in H. apply Nat.leb_le. assumption.
Qed.
Lemma lt_impl_le x y: opt_lt x y = true -> opt_le x y = true.
Proof.
  intros. destruct x, y; simpl in *; try tauto; try discriminate.
  apply Nat.leb_le. apply Nat.ltb_lt in H. lia.
Qed.
Lemma lt_le_dec x y: opt_lt x y = true \/ opt_le y x = true.
Proof.
  intros. destruct x, y; simpl in *; try tauto; try discriminate.
  rewrite Nat.leb_le. rewrite Nat.ltb_lt. lia.
Qed.
Lemma lt_add x y z: opt_lt x y = false -> opt_lt (opt_add x z) y = false.
Proof.
  destruct x, y, z; try tauto.
  simpl. repeat rewrite Nat.ltb_ge. lia.
Qed.
Lemma lt_add' x y z: opt_lt (opt_add x z) y = true -> opt_lt x y = true.
Proof.
  destruct x, y, z; try tauto; try discriminate.
  simpl. repeat rewrite Nat.ltb_lt. lia.
Qed.
Lemma add_in_lt x y: opt_lt (opt_add x y) x = false.
Proof.
  destruct x, y; try tauto.
  simpl. rewrite Nat.ltb_ge. lia.
Qed.
Lemma opt_le_add x y: opt_le x (opt_add x y) = true.
Proof. destruct x, y; try tauto. simpl. rewrite Nat.leb_le. lia. Qed.
Lemma opt_le_add' x y: opt_le x (opt_add y x) = true.
Proof. destruct x, y; try tauto. simpl. rewrite Nat.leb_le. lia. Qed.
Lemma opt_le_siml_add x y z: opt_le y z = true -> opt_le (opt_add x y) (opt_add x z) = true.
Proof. destruct x, y, z; try tauto. simpl in *. intro. apply Nat.leb_le. apply Nat.leb_le in H. lia. Qed.
Lemma opt_le_siml_add' x y z: opt_le y z = true -> opt_le (opt_add y x) (opt_add z x) = true.
Proof. destruct x, y, z; try tauto. simpl in *. intro. apply Nat.leb_le. apply Nat.leb_le in H. lia. Qed.

(* relax v via u avec poids w, sur distances d *)
Definition relax (d : dist) (u v w : nat) : dist :=
  let du := get_dist d u in
  let dv := get_dist d v in
  let cand := opt_add du (Some w) in
  if opt_lt cand dv
  then update_dist d v cand
  else d.

(* lemmas update and relax *)

Lemma get_update d u' x: u' < length d -> nth u' (update_dist d u' x) None = x.
Proof.
  revert u'. induction d; intros; simpl in *; try lia.
  destruct u'; try reflexivity.
  simpl. apply IHd. lia.
Qed.

Lemma length_update d u n: length (update_dist d u n) = length d.
Proof.
  revert u. induction d; try reflexivity.
  simpl. destruct u; try reflexivity.
  simpl. rewrite IHd. reflexivity.
Qed.
Lemma length_relax d u n n0: length (relax d u n n0) = length d.
Proof.
  unfold relax. destruct (opt_lt (opt_add (get_dist d u) (Some n0)) (get_dist d n)); try reflexivity.
  rewrite length_update. reflexivity.
Qed.

Lemma update_other d u' n x: n <> u' ->  nth u' (update_dist d n x) None = nth u' d None.
  revert n u'. induction d; try reflexivity.
  simpl. destruct n, u'; try reflexivity; try contradiction.
  intro. apply IHd. lia.
Qed.

Lemma relax_other d u u' n n0 : n <> u' ->  nth u' (relax d u n n0) None = nth u' d None.
Proof.
  intro. unfold relax; simpl.
  destruct (opt_lt (opt_add (get_dist d u) (Some n0)) (get_dist d n)); try reflexivity.
  apply update_other. lia.
Qed.

Lemma relax_u d u n n0: nth u (relax d u n n0) None = nth u d None.
Proof.
  unfold relax; simpl. destruct (opt_lt (opt_add (get_dist d u) (Some n0)) (get_dist d n)) eqn:Hdis; try reflexivity; destruct (Nat.eq_dec n u).
  - rewrite e in Hdis. rewrite add_in_lt in Hdis. discriminate.
  - apply update_other. assumption.
Qed.

Lemma relax_orthogonal d d' l u u':
  length d = length d' -> nth u' d None = nth u' d' None -> nth u d None = nth u d' None -> nth u' (fold_left (fun (acc : dist) '(v, w) => relax acc u v w) l d) None = nth u' (fold_left (fun (acc : dist) '(v, w) => relax acc u v w) l d') None.
Proof.
  revert d d'. induction l; intros; try assumption.
  simpl. apply IHl.
  - destruct a. repeat rewrite length_relax. assumption.
  - destruct a. destruct (Nat.eq_dec n u').
  --unfold relax, get_dist. rewrite e. rewrite H0. rewrite H1.
    destruct (opt_lt (opt_add (nth u d' None) (Some n0)) (nth u' d' None)).
    + destruct (le_lt_dec (length d) u').
      * rewrite nth_overflow. rewrite nth_overflow. reflexivity.
        all: rewrite length_update; lia.
      * pose proof l0. rewrite H in l0. repeat rewrite get_update; try assumption. reflexivity.
    + assumption.
  --repeat rewrite relax_other; try assumption.
  - destruct a. repeat rewrite relax_u. assumption.
Qed.



(* Dijkstra *)

(* suppose que tu as déjà: voisins : nat -> list (nat * nat) *)
Definition neighbors (G:Graph) (i:nat): list (nat * nat) := nth i G [].

Function dijkstra_loop G pq d {measure length pq} : dist :=
  match extract_min pq d with
  | None => d
  | Some (u, pq') =>
      let d' :=
        fold_left (fun acc '(v,w) => relax acc u v w)
                  (neighbors G u) d
      in dijkstra_loop G pq' d'
  end.
Proof.
  intros. unfold extract_min in teq.
  destruct pq.
  - discriminate teq.
  - replace pq' with (remove Nat.eq_dec (argmin_nonempty d n pq) (n :: pq)) by (injection teq as H; auto).
    apply remove_decreases. apply argmin_nonempty_correct.
Qed.

Definition dijkstra (G:Graph) (src : nat) : dist :=
  let n := length G in
  let d0 := init_dist n src in
  let pq0 := init_pq n in
  dijkstra_loop G pq0 d0.



(* Exemple d’invariant : à chaque étape, les distances sont correctes
   pour les sommets déjà extraits, et majorantes pour les autres. *)
Definition dijkstra_invariant (G:Graph) (H_cons: consistent_weigth G) (src:nat) (pq:pqueue) (d:dist) :=
  (forall u, vertex_is_in G u -> ~ In u pq -> minimum_dist_from_to_is_restr G (nth u d None) pq src u H_cons) /\
  (forall u, vertex_is_in G u -> In u pq -> minimum_dist_from_to_restr G (nth u d None) pq src u H_cons) /\
  length G = length d.

Lemma init_pq_full G u : vertex_is_in G u -> In u (init_pq (length G)).
Proof.
  intro. unfold vertex_is_in in H. induction (length G); try lia.
  assert (u=n \/ u<n) by lia. destruct H0;
  try (rewrite H0); simpl; tauto.
Qed.

Lemma init_dist_src src n: src < n -> nth src (init_dist n src) None = Some 0.
Proof.
  revert src.
  induction n; intros; try lia.
  destruct src; try reflexivity.
  simpl. replace (src-0) with src by lia. apply IHn. lia.
Qed.

Lemma init_dist_others src u n: u<>src -> nth u (init_dist n src) None = None.
Proof.
  revert src u.
  induction n; intros.
  - destruct u; reflexivity.
  - simpl. destruct src.
    + rewrite Nat.eqb_refl. simpl. destruct u; try contradiction. apply nth_repeat.
    + assert (S src <> 0) by lia. apply Nat.eqb_neq in H0. rewrite H0.
      simpl. destruct u; try reflexivity.
      replace (src-0) with src by lia. apply IHn. lia.
Qed.

Lemma init_no_path G  src u0: u0 <> src -> ~ (exists p : Path, is_path_from_to_restr G p (init_pq (length G)) src u0).
Proof.
  intro. intro. destruct H0 as [[|x p] H0]; try contradiction.
  destruct p; simpl in H0; try lia.
  destruct H0 as [[H0 [H1 _]] _]. apply init_pq_full in H1. contradiction.
Qed.

Lemma init_length n src: n = length (init_dist n src).
Proof. revert src. induction n; try reflexivity.
  intro. simpl. destruct (src =? 0); simpl.
  - rewrite repeat_length. reflexivity.
  - rewrite <- IHn. reflexivity.
Qed.

Lemma dijkstra_init_invariant :
  forall G (H_cons: consistent_weigth G) src u pq',
    let n := length G in
    let d := init_dist n src in
    let pq := init_pq n in
    extract_min pq d = Some (u, pq') ->
    let d' :=
      fold_left (fun acc '(v,w) => relax acc u v w) (neighbors G u) d in
    dijkstra_invariant G H_cons src pq d.
Proof.
  (*essayer avec l'invariant vrai meme au debut ?*)
  intros. repeat split; intros.
  - exfalso. unfold pq in H1.
    absurd (In u0 (init_pq (length G))); try assumption.
    apply init_pq_full in H0. contradiction.
  - assert (u0 = src \/ u0 <> src) by lia. destruct H2.
    + right. exists [src]. simpl. rewrite H2 in *.
      assert (nth src d None = Some 0). apply init_dist_src. assumption.
      repeat split; try tauto.
      intros. rewrite H3. destruct (path_weight' G p'); try tauto.
    + left. split.
      * apply init_no_path. assumption.
      * apply init_dist_others. assumption.
  - unfold d. fold n. apply init_length.
Qed.

(* changed, unchanged *)

Lemma dist_le_u_unchanged G d u u':
  let d' := (fold_left (fun (acc : dist) '(v, w) => relax acc u v w) (neighbors G u) d) in
  opt_le (get_dist d u') (get_dist d u) = true -> get_dist d u' = get_dist d' u'.
Proof.
  intros. unfold get_dist, neighbors in *.
  induction (nth u G []).
  - reflexivity.
  - set (d'' := fold_left (fun (acc : dist) '(v, w) => relax acc u v w) l d).
    assert (nth u' d' None = nth u' d'' None).
    {
      simpl in d'. destruct a. apply relax_orthogonal.
      + apply length_relax.
      + unfold relax, get_dist. destruct (Nat.eq_dec n u').
        * rewrite e. apply rel_opt_le_lt in H. apply (lt_add _ _ (Some n0)) in H. rewrite H. reflexivity.
        * destruct (opt_lt (opt_add (nth u d None) (Some n0)) (nth n d None)).
          **apply update_other; assumption.
          **reflexivity.
      + apply relax_u.
    }
    rewrite H0. apply IHl.
Qed.

Lemma dist_ge_u_ge_relax d u u' n n0: opt_le (nth u d None) (nth u' d None) = true -> opt_le (nth u d None) (nth u' (relax d u n n0) None) = true.
Proof.
  intros. unfold relax. destruct (opt_lt (opt_add (get_dist d u) (Some n0)) (get_dist d n)) eqn:Hdis.
  - destruct (Nat.eq_dec n u').
    + destruct (Nat.lt_ge_cases u' (length d)).
      * rewrite e. rewrite get_update. apply opt_le_add. assumption.
      * rewrite <- (length_update d n (opt_add (get_dist d u) (Some n0))) in H0. rewrite (nth_overflow _ _ H0). destruct (nth u d None); reflexivity.
    + rewrite update_other; assumption.
  - assumption.
Qed.

Lemma dist_ge_u_ge G d u u':
  let d' := (fold_left (fun (acc : dist) '(v, w) => relax acc u v w) (neighbors G u) d) in
  opt_le (get_dist d u) (get_dist d u') = true -> opt_le (get_dist d u) (get_dist d' u') = true.
Proof.
  unfold get_dist, neighbors in *. revert d. induction (nth u G []); intros.
  - assumption.
  - simpl.  destruct a. apply (dist_ge_u_ge_relax d u u' n n0) in H.
    rewrite <- (relax_u d u n n0) in H. specialize (IHl _ H).
    assert (opt_le (nth u d None) (nth u (relax d u n n0) None) = true). rewrite relax_u. apply opt_le_refl.
    apply (opt_le_trans _ _ _ H0 IHl).
Qed.

Lemma dist_u_unchanged_in_d' G d u:
  let d' := (fold_left (fun (acc : dist) '(v, w) => relax acc u v w) (neighbors G u) d) in
  get_dist d u = get_dist d' u.
Proof.
  apply (dist_le_u_unchanged G d u u).
  apply opt_le_refl.
Qed.
Lemma dist_u_unchanged_in_d'_ G d u:
  let d' := (fold_left (fun (acc : dist) '(v, w) => relax acc u v w) (neighbors G u) d) in
  nth u d None = nth u d' None.
Proof.
  apply (dist_le_u_unchanged G d u u).
  apply opt_le_refl.
Qed.

Lemma not_adj_unchanged_aux_gnl l d d' u u0: ~ (exists w : nat, In (u0, w) l) -> nth u0 d' None = nth u0 d None -> nth u0 (fold_left (fun (acc : dist) '(v, w) => relax acc u v w) l d') None = nth u0 d None.
Proof.
  revert d'. induction l; intros; try assumption.
  simpl. destruct a. apply IHl.
  - intro. absurd (exists w : nat, In (u0, w) ((n, n0) :: l)); try assumption.
    destruct H1. exists x. right. assumption.
  - assert (n<>u0). intro. absurd (exists w : nat, In (u0, w) ((n, n0) :: l)); try assumption. exists n0. left. rewrite H1. reflexivity.
    rewrite (relax_other d' u _ _ n0 H1). assumption.
Qed.
Lemma not_adj_unchanged_aux G d d' u u0: ~ (exists w : nat, In (u0, w) (nth u G [])) -> nth u0 d' None = nth u0 d None -> nth u0 (fold_left (fun (acc : dist) '(v, w) => relax acc u v w) (neighbors G u) d') None = nth u0 d None.
Proof. apply not_adj_unchanged_aux_gnl. Qed.
Lemma not_adj_unchanged G d u u0: ~ (exists w : nat, In (u0, w) (nth u G [])) -> nth u0 (fold_left (fun (acc : dist) '(v, w) => relax acc u v w) (neighbors G u) d) None = nth u0 d None.
Proof. intro. apply not_adj_unchanged_aux. 1:assumption. 1:reflexivity. Qed.

(* pour too_far_unchanged_aux_gnl *)
Lemma is_neigh_dec_aux (l: list (nat*nat)) u0: (exists w: nat, In (u0, w) l) \/ ~(exists w: nat, In (u0, w) l).
Proof.
  destruct (In_dec Nat.eq_dec u0 (List.map (fun (p: nat*nat) => let (x, _) := p in x) l)).
  - left. induction l; try contradiction. destruct i.
    + destruct a. exists n0. left. rewrite H. reflexivity.
    + destruct (IHl H). exists x. right. assumption.
  - right. intro. induction l.
    + destruct H. contradiction.
    + destruct H. destruct H.
      * rewrite H in n. simpl in n. tauto.
      * apply IHl.
        **simpl in n. tauto.
        **exists x. assumption.
Qed.

Lemma is_neigh_dec (G: Graph) u u0: (exists w: nat, In (u0, w) (nth u G [])) \/ ~(exists w: nat, In (u0, w) (nth u G [])).
Proof. apply is_neigh_dec_aux. Qed.

Lemma too_far_unchanged_aux_gnl l d d' u u0 w: (forall j w w' : nat, In (j, w) l -> In (j, w') l -> w = w') -> In (u0, w) l -> opt_lt (opt_add (get_dist d' u) (Some w)) (get_dist d' u0) = false -> nth u0 d' None = nth u0 d None -> nth u0 (fold_left (fun (acc : dist) '(v, w) => relax acc u v w) l d') None = nth u0 d None.
Proof.
  revert d'. induction l; intros; try assumption.
  simpl. destruct a. destruct (Nat.eq_dec n u0).
  - assert (w=n0). apply (H _ _ n0 H0 ltac:(rewrite e; left; reflexivity)).
    assert (nth u0 (relax d' u n n0) None = nth u0 d None). {
      unfold relax, get_dist in *. rewrite <- H3. rewrite e. rewrite H1. assumption.
    }
    destruct (is_neigh_dec_aux l u0).
    + destruct H5. unfold consistent_weigth in H. pose proof (H _ _ x H0 ltac:(right; assumption)). rewrite <- H6 in H5.
      apply IHl; try assumption.
      * intros. apply (H j w0 w'); right; assumption.
      * unfold get_dist in *. destruct (Nat.eq_dec n u).
      ++rewrite e0 in *. rewrite H4. unfold relax. rewrite add_in_lt. rewrite <- H2. assumption.
      ++rewrite H4. rewrite relax_other; try assumption. rewrite <- H2. assumption.
    + apply not_adj_unchanged_aux_gnl; assumption.
  - apply IHl; try assumption.
    + intros. apply (H j w0 w'); right; assumption.
    + destruct H0; try assumption. inversion H0. rewrite H4 in n1. contradiction.
    + unfold get_dist in *. destruct (Nat.eq_dec n u).
      ++rewrite e in *. unfold relax. rewrite add_in_lt. assumption.
      ++repeat rewrite relax_other; assumption.
    + rewrite (relax_other d' u _ _ _ n1). assumption.
Qed.
Lemma too_far_unchanged_aux G d d' u u0 w: consistent_weigth G -> In (u0, w) (nth u G []) -> opt_lt (opt_add (get_dist d' u) (Some w)) (get_dist d' u0) = false -> nth u0 d' None = nth u0 d None -> nth u0 (fold_left (fun (acc : dist) '(v, w) => relax acc u v w) (neighbors G u) d') None = nth u0 d None.
Proof. intros. specialize (H u). apply (too_far_unchanged_aux_gnl _ _ _ _ _ w); try assumption. Qed.
Lemma too_far_unchanged G d u u0 w: consistent_weigth G -> In (u0, w) (nth u G []) -> opt_lt (opt_add (get_dist d u) (Some w)) (get_dist d u0) = false -> nth u0 (fold_left (fun (acc : dist) '(v, w) => relax acc u v w) (neighbors G u) d) None = nth u0 d None.
Proof. intros. apply (too_far_unchanged_aux _ _ _ _ _ w); try assumption. reflexivity. Qed.

Lemma d'_updated_aux G d d' u u0 w: consistent_weigth G -> u0 < length d' -> In (u0, w) (nth u G []) -> opt_lt (opt_add (get_dist d u) (Some w)) (get_dist d u0) = true -> nth u0 d' None = nth u0 d None -> nth u d' None = nth u d None -> nth u0 (fold_left (fun (acc : dist) '(v, w0) => relax acc u v w0) (neighbors G u) d') None = opt_add (nth u d None) (Some w).
Proof.
  intro. specialize (H u).
  revert H d'. unfold neighbors. induction (nth u G []); intros; try contradiction.
  simpl. destruct a. destruct (Nat.eq_dec n u0).
  - assert (n0 = w). apply (H _ n0) in H1; try assumption. rewrite e. left. reflexivity.
    assert (nth u0 (relax d' u n n0) None = opt_add (nth u d None) (Some w)). unfold relax, get_dist in *. rewrite e, H5, H4, H3, H2. apply get_update. assumption.
    destruct (is_neigh_dec_aux l u0).
    + rewrite (too_far_unchanged_aux_gnl _ ((relax d' u n n0)) _ _ _ w).
      * assumption.
      * intros. apply (H j w0 w'); right; assumption.
      * destruct H7. assert (x=w) by (apply (H _ x _) in H1; try right; assumption). rewrite H8 in H7. assumption.
      * destruct (Nat.eq_dec u u0); try (rewrite e0; apply add_in_lt).
        unfold get_dist. rewrite H6. rewrite relax_other; try lia.
        rewrite H4. apply rel_opt_le_lt. apply opt_le_refl.
      * reflexivity.
    + rewrite (not_adj_unchanged_aux_gnl l (relax d' u n n0)); tauto.
  - apply IHl; try assumption.
    + intros. apply (H j w0 w'); right; assumption.
    + rewrite length_relax. assumption.
    + destruct H1; try assumption. inversion H1. rewrite H6 in n1. contradiction.
    + rewrite <- H3. apply relax_other. assumption.
    + destruct (Nat.eq_dec n u).
      * unfold relax. rewrite e. rewrite add_in_lt. assumption.
      * rewrite relax_other; assumption.
Qed.
Lemma d'_updated G d u u0 w: consistent_weigth G -> u0 < length d -> In (u0, w) (nth u G []) -> opt_lt (opt_add (get_dist d u) (Some w)) (get_dist d u0) = true -> nth u0 (fold_left (fun (acc : dist) '(v, w0) => relax acc u v w0) (neighbors G u) d) None = opt_add (nth u d None) (Some w).
Proof. intros. apply d'_updated_aux; tauto. Qed.

(* auxilary lemmas *)

Lemma dist_u_min_in_d' G pq pq' d u u':
  let d' := (fold_left (fun (acc : dist) '(v, w) => relax acc u v w) (neighbors G u) d) in
  extract_min pq d = Some (u, pq') -> In u' pq' -> le_by_dist d' u u' = true.
Proof.
  intros.
  pose proof (dist_u_min_in_d pq pq' d u u' H H0).
  unfold le_by_dist, d'.
  rewrite <- (dist_u_unchanged_in_d' G d u).
  exact (dist_ge_u_ge G d u u' H1).
Qed.

Lemma u_in_pq d pq pq' u:
  extract_min pq d = Some (u, pq') -> In u pq.
Proof.
  intro. destruct pq; try discriminate.
  inversion H.
  apply (argmin_nonempty_correct).
Qed.

Lemma in_not_empty_impl_vertex_is_in G u u0 w: In (u0, w) (nth u G []) -> vertex_is_in G u.
Proof. intro. unfold vertex_is_in. destruct (Nat.lt_ge_cases u (length G)); try assumption. rewrite (nth_overflow _ ([]) H0) in H. contradiction. Qed.

(* manipulatin de chemin : découpe, ajout d'arrète *)

(* on ajoute une arrète au debut *)
Lemma path_cut' G pq n1 n u src p'': (exists w : nat, In (n1, w) (nth src G [])) -> vertex_is_in G src -> ~ In src pq -> is_path_from_to_restr G (n1 :: p'') pq n u -> is_path_from_to_restr G (src :: n1 :: p'') pq src u.
Proof.
  intros. destruct p''.
  - simpl in *. repeat split; tauto.
  - unfold is_path_from_to_restr in *. repeat split; try (simpl in *; tauto).
Qed.

(* on retire une arète au debut *)
Lemma path_cut'_rec G pq a n1 u src p'': is_path_from_to_restr G (a :: n1 :: p'') pq src u -> (exists w : nat, In (n1, w) (nth src G [])) /\ vertex_is_in G src /\ ~ In src pq /\ is_path_from_to_restr G (n1 :: p'') pq n1 u.
Proof.
  intro. destruct p''.
  - simpl in *. replace src with a in * by tauto. repeat split; try tauto.
  - unfold is_path_from_to_restr in *. replace src with a in * by tauto. repeat split; try (simpl in *; tauto).
Qed.

(* on ajoute une arrète à la fin *)
Lemma path_cut'' G pq n1 n2 n u p'': (exists w : nat, In (n2, w) (nth n1 G [])) -> vertex_is_in G n2 -> ~ In n1 pq -> is_path_from_to_restr G (p''++[n1]) pq n u -> is_path_from_to_restr G (p''++[n1; n2]) pq n n2.
Proof.
  intros. revert n H2. induction p''; intros.
  - simpl in *. tauto.
  - destruct p''.
    + simpl in *. tauto.
    + pose proof H2. simpl in H3.
      assert (a=n). tauto.
      rewrite <- H4. replace ((a :: n0 :: p'') ++ [n1; n2]) with (a :: n0 :: p'' ++ [n1; n2]) by reflexivity.
      apply (path_cut' _ _ _ n0); try tauto.
      apply IHp''. apply (path_cut'_rec) in H2; try tauto.
Qed.
Lemma path_cut_last G x0 pq src v0: is_path_from_to_restr G x0 pq src v0 -> exists x, x0=x++[v0].
Proof.
  revert src. induction x0; try contradiction. destruct x0.
  - simpl. intro. exists []. simpl. f_equal. tauto.
  - intros. apply path_cut'_rec in H. destruct (IHx0 n ltac:(tauto)).
    exists (a::x). rewrite H0. reflexivity.
Qed.

Lemma path_add_last_vertex G pq n1 n2 n p'': (exists w : nat, In (n2, w) (nth n1 G [])) -> vertex_is_in G n2 -> ~ In n1 pq -> is_path_from_to_restr G (p'') pq n n1 -> is_path_from_to_restr G (p''++[n2]) pq n n2.
Proof.
  intros.
  destruct (path_cut_last G _ pq _ _ H2).
  rewrite H3.
  replace ((x ++ [n1]) ++ [n2]) with (x ++ [n1] ++ [n2]) by apply app_assoc.
  replace (x ++ [n1] ++ [n2]) with (x ++ [n1; n2]) by reflexivity.
  apply (path_cut'' _ _ _ _ _ n1); try tauto. rewrite <- H3. assumption.
Qed.

Lemma extend_path_weigth G a n p w (H_cons: consistent_weigth G): In (n, w) (nth a G []) -> path_weight' G (a :: n :: p) = opt_add (Some w) (path_weight' G (n :: p)).
Proof. intro. simpl. rewrite (find_In_eq _ n w (H_cons a) H). reflexivity. Qed.

Lemma extend_path_weigth_incr G a n p w (H_cons: consistent_weigth G): In (n, w) (nth a G []) -> opt_le (path_weight' G (n :: p)) (path_weight' G (a :: n :: p)) = true.
Proof. intro. rewrite (extend_path_weigth G a n p w (H_cons) H). apply opt_le_add'. Qed.

Lemma path_weigth_increase G p'' p_ (H1: is_path' G p'') (H2: is_path' G (p''++p_)) (H_cons: consistent_weigth G): opt_le (path_weight' G p'') (path_weight' G (p'' ++ p_)) = true.
Proof.
  induction p''.
  - contradiction.
  - destruct p''.
    + cbn [path_weight']. destruct (path_weight' G ([a] ++ p_)); reflexivity.
    + destruct H1 as [_ [[w H3] H1]]. destruct H2 as [_ [_ H2]]. specialize (IHp'' H1 H2).
      rewrite (extend_path_weigth G a n p'' w H_cons H3).
      replace ((a :: n :: p'') ++ p_) with (a :: n :: p'' ++ p_) by reflexivity.
      rewrite (extend_path_weigth G a n (p''++p_) w H_cons H3).
      apply opt_le_siml_add. assumption.
Qed.

Lemma last_path_from_to G x pq src v0: is_path_from_to_restr G x pq src v0 -> last x (v0 + 1) = v0.
Proof.
  revert src. induction x; intros; try contradiction. destruct x.
  - simpl in *. tauto.
  - specialize (IHx n ltac:(simpl in *; destruct x; tauto)).
    simpl in *. assumption.
Qed.

Lemma cut_path_restr_u G d pq pq' p'' src u: extract_min pq d = Some (u, pq') -> is_path_from_to_restr G p'' pq' src u -> exists p : Path, is_path_from_to_restr G p pq src u /\ opt_le (path_weight' G p) (path_weight' G p'') = true.
Proof.
  intro. revert src. induction p''; try contradiction.
  intros. destruct (Nat.eq_dec a u).
  - exists [a]. split.
    + simpl in *. destruct p''; tauto.
    + replace (path_weight' G [a]) with (Some 0) by reflexivity.
      destruct (path_weight' G (a :: p'')); reflexivity.
  - destruct p''.
    + simpl in H0. lia.
    + assert (is_path_from_to_restr G (n0 :: p'') pq' n0 u). destruct p''; simpl in *; try tauto.
      destruct (IHp'' n0 H1) as [p0 [H2 H3]].
      exists (a::p0). split.
      * destruct p0; try contradiction. simpl in H0.
        replace src with a by tauto.
        replace n1 with n0 in * by (destruct p0; simpl in H2; lia).
        apply (path_cut' _ _ _ n0); try tauto.
        apply (not_in_pq' _ _ _ u a) in H; tauto.
      * destruct p0; try contradiction.
        replace n1 with n0 in * by (destruct p0; simpl in H2; lia).
        (* on pourrait faire un lemme pour ce qui suit *)
        simpl in *. destruct (find (fun '(k, _) => k =? n0) (nth a G [])).
        ++destruct p. pose proof (opt_le_siml_add).
          specialize (H4 (Some n3) _ _ H3). simpl in H4. exact H4.
        ++reflexivity.
Qed.

(* path manipulation : last edge *)

Lemma last_edge__ G p pq' src u0: p <> [u0] -> In u0 pq' -> is_path_from_to_restr G p pq' src u0 -> exists p' v0, is_path_from_to_restr G [v0;u0] pq' v0 u0 /\ is_path_from_to_restr G p' pq' src v0 /\ p=p'++[u0].
Proof.
  intros. revert src H1 H. induction p; try contradiction. intros. destruct p.
  - destruct H1 as [_[_ H1]]. rewrite H1 in H. contradiction.
  - destruct p.
    + exists [a], a.
      assert (n=u0). { simpl in H1. tauto. } rewrite H2 in H1.
      assert (src=a). { simpl in H1. lia. } rewrite H3 in H1.
      simpl in *. repeat split; try tauto.
      * lia.
      * rewrite H2. reflexivity.
    + assert (is_path_from_to_restr G (n :: n0 :: p) pq' n u0). simpl in H1. repeat split; tauto.
      assert (n :: n0 :: p <> [u0]). injection. intro. discriminate.
      destruct (IHp n H2 H3) as [p' [v0 [H4 [H5 H6]]]].
      exists (src::p'), v0. split; try assumption.
      (* H1 => a=src et a -> n , H5 => .*)
      unfold is_path_from_to in *. destruct p'; try (destruct H5; contradiction).
      simpl in H1.
      assert (a=src). tauto.
      assert (n1=n). inversion H6. reflexivity.
      rewrite H7 in *. rewrite H8 in *.
      repeat split; try tauto.
      * simpl in H5. simpl. destruct p'; tauto.
      * simpl in H5. simpl. destruct p'; tauto.
      * rewrite H6. reflexivity.
Qed.

Lemma last_edge_ G p pq' src u0: p <> [u0] -> In u0 pq' -> is_path_from_to_restr G p pq' src u0 -> exists p' v0, is_path_from_to_restr G [v0;u0] pq' v0 u0 /\ is_path_from_to G p' src v0.
Proof. intros. destruct (last_edge__ _ _ _ _ _ H H0 H1) as [p' [v0 [H2 [H3 _ ]]]]. exists p', v0. apply rest_is_not_restr in H3. tauto. Qed.

Lemma assoc_opt_add_weigth_path e w n1: match opt_add e (Some w) with | Some w' => Some (n1 + w') | None => None end = opt_add match e with | Some w' => Some (n1 + w') | None => None end (Some w).
Proof. destruct e; try reflexivity. simpl. f_equal. lia. Qed.

Lemma weight_add_vertex_end G p u0 v0 w: consistent_weigth G -> last p (v0+1) = v0 -> In (u0, w) (nth v0 G []) -> path_weight' G (p++[u0]) = opt_add (path_weight' G (p)) (Some w).
Proof.
  intros. induction p; try (simpl in H0; lia). destruct p.
  - simpl. unfold consistent_weigth in H. simpl in H0. rewrite H0. rewrite (find_In_eq _ _ _ (H v0) H1). f_equal. lia.
  - specialize (IHp ltac:(simpl; simpl in H0; assumption)).
  simpl. simpl in IHp. rewrite IHp.
  destruct (find (fun '(k, _) => k =? n) (nth a G [])); try reflexivity.
  destruct p0. apply assoc_opt_add_weigth_path.
Qed.

(* is path -> finite weigth *)

Lemma is_path_from_to_restr_finite_weigth G x0 pq src u0: consistent_weigth G -> is_path_from_to_restr G x0 pq src u0 -> exists w, path_weight' G x0 = Some w.
Proof.
  intros.
  assert (is_path G x0). apply (path_equiv_2 G x0 H). apply (is_path_from_to_restr_IS_A_PATH _ _ pq src u0 H0).
  exists (path_weight G x0 H1). apply path_weigth_equiv_2. assumption.
Qed.

Lemma is_path_from_to_restr_finite_weigth' G x0 pq src u0: consistent_weigth G -> is_path_from_to_restr G x0 pq src u0 -> path_weight' G x0 = None -> False.
Proof. intros. destruct (is_path_from_to_restr_finite_weigth G x0 pq src u0 H H0). rewrite H1 in H2. discriminate. Qed.

Lemma is_path_from_to_restr_finite_weigth'' G x0 pq src u0: consistent_weigth G -> is_path_from_to_restr G x0 pq src u0 -> None = path_weight' G x0 -> False.
Proof. intros. destruct (is_path_from_to_restr_finite_weigth G x0 pq src u0 H H0). rewrite <- H1 in H2. discriminate. Qed.

(* propriété restr path *)

Lemma is_restr_dec G p' pq src u: is_path_from_to G p' src u -> is_path_from_to_restr G p' pq src u \/ (exists u_ p_ p'', In u_ pq /\ p' = p'' ++ p_ /\ is_path_from_to_restr G p'' pq src u_).
Proof.
  revert src. induction p'; try contradiction; intros. destruct p'.
  - simpl in *. tauto.
  - destruct (In_dec Nat.eq_dec a pq).
    + right. exists a, (n::p'), [a]. unfold is_path_from_to, is_path' in H. repeat split; try tauto.
    + apply path_cut in H. destruct H. destruct (IHp' n H0).
      * left. destruct H as [H_ [H H2]]. unfold is_path' in H_. rewrite H in *.
        apply (path_cut' _ _ _ n); try tauto.
      * right. destruct H1 as [u_ [p_ [p'' H1]]]. exists u_, p_, (a::p''). repeat split; try tauto.
        ++simpl. f_equal. tauto.
        ++destruct p''; try (simpl in *;tauto). destruct H as [[H H_] [H2 _]].
          destruct H1 as [_ [H1 H4]]. simpl in H1. inversion H1.
          rewrite H5 in H_. rewrite H2 in *. apply (path_cut' _ _ _ n); try tauto.
Qed.

Lemma is_restr_cut_aux1 G d p pq pq' src u0 u: extract_min pq d = Some (u, pq') -> is_path_from_to_restr G p pq' src u0 -> In u p -> (exists p_ p', p = p' ++ p_ /\ is_path_from_to_restr G p' pq src u).
Proof.
  intro. revert src. induction p; try contradiction. intros. destruct (Nat.eq_dec u a).
  - exists p, [a].
    assert (vertex_is_in G a /\ a = src). unfold is_path_from_to_restr, is_path_restr in H0; destruct p; tauto.
    rewrite e. simpl. tauto.
  - destruct H1; try lia. destruct p; try contradiction.
    destruct (path_cut'_rec _ _ _ _ _ _ _ H0) as [_ [_ [_ H2]]].
    destruct (IHp n0 H2 H1) as [p_ [p' [H3 H4]]]. exists p_, (a::p').
    split.
    + rewrite H3. reflexivity.
    + assert (vertex_is_in G a /\ a = src). unfold is_path_from_to_restr, is_path_restr in H0; destruct p; tauto.
      destruct p'.
      * simpl in *. tauto.
      * destruct H5. rewrite <- H6. apply (path_cut' _ _ _ n0); try assumption.
        unfold is_path_from_to_restr, is_path_restr in H0.
        ++assert(n1=n0). unfold is_path_from_to_restr in H4. destruct p'; tauto.
          rewrite H7. tauto.
        ++assert (~(In a pq')). unfold is_path_from_to_restr, is_path_restr in H0. tauto.
        destruct (not_in_pq' pq pq' d _ _ H H7); try lia. assumption.
Qed.
Lemma is_restr_cut_aux2_ G d p pq pq' u: extract_min pq d = Some (u, pq') -> is_path_restr G p pq' -> ~(In u p) -> is_path_restr G p pq.
Proof.
  intros. induction p; try contradiction. destruct p; try tauto.
  repeat split; try (simpl in *; tauto).
  destruct (not_in_pq' _ _ _ u a H ltac:(simpl in H0; tauto)).
  + simpl in H1. absurd (a=u); tauto.
  + assumption.
Qed. 
Lemma is_restr_cut_aux2 G d p pq pq' src u0 u: extract_min pq d = Some (u, pq') -> is_path_from_to_restr G p pq' src u0 -> ~(In u p) -> is_path_from_to_restr G p pq src u0.
Proof.
  intros. destruct p; try contradiction. destruct p; try (simpl in *; tauto).
  unfold is_path_from_to_restr in *. split; try tauto. destruct H0 as [H0 _].
  apply (is_restr_cut_aux2_ G d _ pq pq' u H H0 H1).
Qed.
Lemma is_restr_cut G d p pq pq' src u0 u: extract_min pq d = Some (u, pq') -> is_path_from_to_restr G p pq' src u0 -> is_path_from_to_restr G p pq src u0 \/ (exists p_ p', p = p' ++ p_ /\ is_path_from_to_restr G p' pq src u).
Proof.
  intros. destruct (In_dec Nat.eq_dec u p).
  - right. apply (is_restr_cut_aux1 _ _ _ _ _ _ _ _ H H0 i).
  - left. apply (is_restr_cut_aux2 _ _ _ _ _ _ _ _ H H0 n).
Qed.

Lemma last_restr_in_G G p'' pq src u_: is_path_from_to_restr G p'' pq src u_ -> vertex_is_in G u_.
Proof. intro. apply rest_is_not_restr in H. apply ext_in_G in H. tauto. Qed.

Lemma path_from_to_rest_weigth G p' pq src u_: consistent_weigth G -> is_path_from_to_restr G p' pq src u_ -> None = path_weight' G p' -> False.
Proof.
  intros.
  assert (is_path G p'). apply path_equiv_2; try assumption. apply (is_path_from_to_restr_IS_A_PATH _ _ _ _ _ H0).
  rewrite (path_weigth_equiv_2 G p' H H2) in H1.
  discriminate.
Qed.

Lemma pq'_inc_pq_ d pq pq' u u0: extract_min pq d = Some (u, pq') -> ~In u0 pq -> ~ In u0 pq'.
Proof. intros. intro. pose proof (pq'_inc_pq d pq pq' u u0 H H1). contradiction. Qed.

Lemma restr_descrease G d p pq pq' u : extract_min pq d = Some (u, pq') -> is_path_restr G p pq -> is_path_restr G p pq'.
Proof.
  intros. induction p; try contradiction. destruct p; try assumption.
  pose proof (pq'_inc_pq_ d pq pq' u a H). split; try (simpl in *; tauto).
Qed.
Lemma restr_descrease_from_to G d p pq pq' src u u0 : extract_min pq d = Some (u, pq') -> is_path_from_to_restr G p pq src u0 -> is_path_from_to_restr G p pq' src u0.
Proof.
  intros. destruct p; try contradiction. destruct p; try assumption.
  unfold is_path_from_to_restr at 1. split; try (simpl in *; tauto).
  destruct H0 as [H0 _]. apply (restr_descrease G d _ pq pq' u H H0).
Qed.

Lemma restr_descrease_min_dist G d pq pq' src u u0 (H_cons:consistent_weigth G): extract_min pq d = Some (u, pq') -> minimum_dist_from_to_is_restr G (nth u0 d None) pq src u0 H_cons -> minimum_dist_from_to_is_restr G (nth u0 d None) pq' src u0 H_cons.
Proof.
  intros. unfold minimum_dist_from_to_is_restr in *.
  destruct H0; try tauto.
  right. destruct H0. exists x. repeat split; try tauto. apply (restr_descrease_from_to G d x pq pq' src u u0); tauto.
Qed.


(* length *)

Lemma lengthd_eq_length_d'_aux l u (d d': dist): length d' = length d -> length (fold_left (fun (acc : dist) '(v, w) => relax acc u v w) l d') = length d.
Proof. revert d'. induction l; simpl; intros; try tauto. apply IHl. destruct a. rewrite <- H. apply length_relax. Qed.
Lemma lengthd_eq_length_d'_ l u (d: dist): length (fold_left (fun (acc : dist) '(v, w) => relax acc u v w) l d) = length d.
Proof. apply lengthd_eq_length_d'_aux. reflexivity. Qed.
Lemma lengthd_eq_length_d' G u (d: dist): length (fold_left (fun (acc : dist) '(v, w) => relax acc u v w) (neighbors G u) d) = length d.
Proof. apply lengthd_eq_length_d'_aux. reflexivity. Qed.

(* dist properties *)

Lemma dist_decrease_l l d u u0:
  let d' := fold_left (fun (acc : dist) '(v, w) => relax acc u v w) l d in
  opt_le (get_dist d' u0) (get_dist d u0) = true.
Proof.
  destruct (Nat.lt_ge_cases u0 (length d)).
  --revert d H. induction l; intros; simpl.
    - apply opt_le_refl.
    - destruct a. apply (opt_le_trans _ ((get_dist (relax d u n n0) u0)) _).
      + apply IHl. rewrite length_relax. assumption.
      + destruct (Nat.eq_dec n u0).
        * unfold relax. destruct (opt_lt (opt_add (get_dist d u) (Some n0)) (get_dist d n))  eqn:Hdis.
        ++rewrite e in *. simpl. unfold get_dist. rewrite (get_update _ _ _ H). apply lt_impl_le. assumption.
        ++apply opt_le_refl.
        * unfold get_dist. rewrite (relax_other _ _ _ _ _ n1). apply opt_le_refl.
  --unfold get_dist. rewrite (nth_overflow _ _ H).
    replace (length d) with (length (fold_left (fun (acc : dist) '(v, w) => relax acc u v w) l d)) in H by (apply lengthd_eq_length_d'_).
    rewrite (nth_overflow _ _ H). apply opt_le_refl.
Qed.

Lemma dist_decrease G d u u0:
  let d' := fold_left (fun (acc : dist) '(v, w) => relax acc u v w) (neighbors G u) d in
  opt_le (get_dist d' u0) (get_dist d u0) = true.
Proof. apply dist_decrease_l. Qed.

Lemma adj_d'_smaller G d u u0 w (H_u0_in: vertex_is_in G u0) (H_lenGd: length G = length d):
  let d' := fold_left (fun (acc : dist) '(v, w) => relax acc u v w) (neighbors G u) d in
  consistent_weigth G -> In (u0, w) (nth u G []) -> opt_le (nth u0 d' None) (opt_add (nth u d None) (Some w)) = true.
Proof.
  simpl. intros. unfold neighbors.
  unfold consistent_weigth in H. specialize (H u).
  induction (nth u G []); try contradiction.
  destruct a.
  destruct (Nat.eq_dec n u0).
  - unfold consistent_weigth in H.
    simpl. pose proof (dist_decrease_l l (relax d u n n0) u u0). unfold get_dist in H1. simpl in H1.
    apply (opt_le_trans _ _ _ H1).
    assert (n0=w). apply (H u0); try assumption. rewrite e. left. reflexivity.
    rewrite H2 in *. rewrite e in *.
    unfold relax, get_dist. destruct (opt_lt (opt_add (nth u d None) (Some w)) (nth u0 d None)) eqn:Hdis.
    + rewrite get_update. apply opt_le_refl.
      (* ici on a besoin de length d  = length G *)
      unfold vertex_is_in in H_u0_in.
      rewrite <- H_lenGd. assumption.
    + apply rel_opt_le_lt. assumption.
  - destruct H0.
    + inversion H0. contradiction.
    + simpl. rewrite (relax_orthogonal (relax d u n n0) d l u u0).
      * assert (forall j w w' : nat, In (j, w) l -> In (j, w') l -> w = w'). intros. apply (H j); simpl; tauto.
        apply (IHl H1 H0).
      * apply length_relax.
      * unfold relax, get_dist. destruct (opt_lt (opt_add (nth u d None) (Some n0)) (nth n d None)).
        **apply update_other. assumption.
        **reflexivity.
      * apply relax_u.
Qed.

Lemma adj_d'_smaller' G d u u0 x0 w (H_u0_in: vertex_is_in G u0) (H_lenGd: length G = length d):
  let d' := fold_left (fun (acc : dist) '(v, w) => relax acc u v w) (neighbors G u) d in
  consistent_weigth G -> nth u d None = Some x0 -> In (u0, w) (nth u G []) -> exists x1, nth u0 d' None = Some x1.
Proof.
  simpl. intros.
  destruct (nth u0 (fold_left (fun (acc : dist) '(v, w) => relax acc u v w) (neighbors G u) d) None) eqn:H2.
  - exists n. reflexivity.
  - exfalso. pose proof (adj_d'_smaller G d u u0 w H_u0_in H_lenGd H H1).
    rewrite H0 in H3. rewrite H2 in H3. discriminate H3.
Qed.



Lemma step_preserves_invariant :
  forall G (H_cons: consistent_weigth G) src pq d u pq',
    dijkstra_invariant G H_cons src pq d ->
    extract_min pq d = Some (u, pq') ->
    let d' :=
      fold_left (fun acc '(v,w) => relax acc u v w) (neighbors G u) d in
    dijkstra_invariant G H_cons src pq' d'.
Proof.
  intros G H_cons src pq d u pq' Hinv Hex.
  destruct Hinv as [Hinv_npq [Hinv_pq Hinv_]].
  repeat split; intros.
  - destruct (not_in_pq' pq pq' d u u0 Hex H0).
    + pose proof (u_in_pq _ _ _ _ Hex). rewrite H1 in *. pose proof Hinv_pq as Hinv_pq_. specialize (Hinv_pq u H H2).
      unfold minimum_dist_from_to. unfold minimum_dist_from_to_restr in Hinv_pq.
      destruct (nth u (fold_left (fun (acc : dist) '(v, w) => relax acc u v w) (neighbors G u) d) None) eqn:Hd.
      * right. rewrite <- dist_u_unchanged_in_d'_ in Hd. destruct Hinv_pq.
        ** rewrite Hd in H3. destruct H3 as [_ H3]. discriminate H3.
        **destruct H3 as [p [H3 [H4 H5]]]. exists p. repeat split; try tauto.
          ++apply (restr_descrease_from_to _ _ _ _ _ _ _ _ Hex H3).
          ++rewrite <- Hd. assumption.
          ++rewrite <- Hd. intros. destruct (is_restr_dec G p' pq src u H6). (* MQ optimal pour les rests -> optimal : on destruct is_restr p' : soit on est restr, soit on passe par un "detour" *)
           ***rapply H5. exact H7.
           ***destruct H7 as [u_ [p_ [p'' H7]]]. pose proof (path_weigth_increase G p'' p_). replace (p'' ++ p_) with p' in H8 by tauto.
              specialize (H8 ltac:(apply (is_path_from_to_restr_IS_A_PATH G p'' pq src u_); tauto) (is_path_from_to_IS_A_PATH G p' src u H6) H_cons).
              apply (opt_le_trans _ (path_weight' G p'') _); try assumption.
              (* utiliser la minimalité de (nth u d None) dans le extract et de (nth u_ d None) dans les rests path *)
              pose proof (dist_u_min_in_d_ _ _ _ _ u_ Hex ltac:(tauto)). unfold le_by_dist, get_dist in H9.
              apply (opt_le_trans _ (nth u_ d None) _); try assumption.
              assert (vertex_is_in G u_). apply (last_restr_in_G G p'' pq src u_). tauto.
              specialize (Hinv_pq_ u_ H10 ltac:(tauto)). destruct Hinv_pq_.
             +++absurd (exists p'', is_path_from_to_restr G p'' pq src u_); try tauto. exists p''. tauto.
             +++destruct H11. apply H11. tauto.
      * left. split; try reflexivity. rewrite <- dist_u_unchanged_in_d'_ in Hd. destruct Hinv_pq.
        ++intro. destruct H4. destruct (is_restr_dec _ _ pq _ _ H4).
          **absurd (exists p : Path, is_path_from_to_restr G p pq src u); try tauto. exists x. assumption.
          **destruct H5 as [u_ [_ [p [H5 [_ H6]]]]].
            (* montrer In u_ pq -> ~(is_path_from_to_restr G p pq src u_) 
            vrai car dist inf pour u, donc dist inf pour tout pq, donc pas de chemin (on destruct Hinv_pq_) *)
            assert (nth u_ d None = None). pose proof (dist_u_min_in_d_ pq pq' d u u_ Hex H5). unfold le_by_dist, get_dist in H7. rewrite Hd in H7. destruct (nth u_ d None). 1:discriminate H7. 1:reflexivity.
            destruct (Hinv_pq_ u_ (last_restr_in_G _ _ _ _ _ H6) H5).
           ***absurd (exists p, is_path_from_to_restr G p pq src u_); try tauto.
              exists p. assumption.
           ***destruct H8 as [p' [H8 [H9 _]]]. rewrite H7 in H9.
              apply (path_from_to_rest_weigth _ _ _ _ _ H_cons H8 H9).
        ++fold get_dist in Hd.
          destruct H3 as [p [H3 [H4 _]]]. rewrite Hd in H4. exfalso.
          apply (path_from_to_rest_weigth _ _ _ _ _ H_cons H3 H4).
    + destruct (is_neigh_dec G u u0).
      * destruct H2 as [w H2]. rewrite (too_far_unchanged _ _ _ _ w); try assumption.
        **apply (restr_descrease_min_dist G d pq pq' src u u0 H_cons Hex).
          apply Hinv_npq; assumption.
        **apply rel_opt_le_lt. pose proof (u_in_pq _ _ _ _ Hex).
          pose proof (in_not_empty_impl_vertex_is_in G u u0 w H2).
          unfold get_dist.
          destruct (Hinv_pq u H4 (u_in_pq _ _ _ _ Hex)).
          ++destruct H5. rewrite H6. destruct (nth u0 d None); reflexivity.
          ++destruct H5 as [p [H5 [ H6 _]]]. rewrite H6.
            rewrite <- (weight_add_vertex_end G p u0 u w H_cons (last_path_from_to G p pq src u H5) H2).
            pose proof (rest_is_not_restr _ _ _ _ _ (path_add_last_vertex _ pq' _ _ src p ltac:(exists w; exact H2) H (remove_removes_all _ _ _ _ Hex) (restr_descrease_from_to _ _ _ _ _ _ _ _ Hex H5))).
            destruct (Hinv_npq u0 H H1).
            --absurd (exists p, is_path_from_to G p src u0); try tauto. exists (p ++ [u0]). assumption.
            --destruct H8 as [_ [_ [_ H8]]]. apply H8. assumption.
      * rewrite not_adj_unchanged; try assumption.
        apply (restr_descrease_min_dist G d pq pq' src u u0 H_cons Hex).
        apply Hinv_npq; assumption.
  - unfold minimum_dist_from_to_restr. destruct (nth u0 (fold_left (fun (acc : dist) '(v, w) => relax acc u v w) (neighbors G u) d) None) eqn:Hdis.
    + right. (* disjonction en fct de si le pds a change ou pas pour construire p, et après disjonction sur le dernier sommet de p' avant u0 *)
      destruct (is_neigh_dec G u u0). (* disjonction u -> u0 *)
      * (* disjonction sur "peut on améliorer le chemin" : test relax *)
        destruct H1 as [w H1]. destruct (opt_lt (opt_add (get_dist d u) (Some w)) (get_dist d u0)) eqn:Hdis2.
        ++(* on améliore la distance : chemin : (chemin opti pour u) ++ u0 *)
          assert (get_dist d u <> None). intro. rewrite H2 in Hdis2. simpl in Hdis2. discriminate.
          pose proof (in_not_empty_impl_vertex_is_in G u u0 w H1).
          destruct (Hinv_pq u H3 (u_in_pq _ _ _ _ Hex)).
          1:unfold get_dist in H2; destruct H4; rewrite H5 in H2; contradiction.
          (* p chemin optimal de src à u *)
          destruct H4 as [p [H4 [H5 H6]]].
          assert (Some n = path_weight' G (p ++ [u0])). {
            (* Mq chemin bien mis à jour : d'[u0] = (path_weight' G p) + w ici parce que Hdis2 donc d' mis a jour *)
            rewrite (weight_add_vertex_end G p u0 u w H_cons (last_path_from_to G p pq src u ltac:(tauto)) H1).
            rewrite <- Hdis. rewrite <- H5.
            apply (d'_updated G d u u0 w); try assumption.
            unfold vertex_is_in in H. rewrite Hinv_ in H. assumption.
          }
          exists (p++[u0]). repeat split.
            **apply (path_add_last_vertex _ _ u _ _ _ ltac:(exists w; exact H1) H (remove_removes_all _ _ _ u Hex)).
              apply (restr_descrease_from_to _ _ _ _ _ _ _ _ Hex H4).
            **assumption.
            **intros. pose proof (pq'_inc_pq _ _ _ _ _ Hex H0).
              {
                (* **MONTRER QUE LE CHEMIN EST OPTIMAL** *)
                (* traiter le cas u0 = src à part *)
                destruct (Nat.eq_dec n 0). rewrite e. destruct (path_weight' G p'); reflexivity.
                assert (p' <> [u0]). { (* faire un lemma pour ca ? *)
                  intro. rewrite H10 in H8. simpl in H8.
                  (* mq u0 = src est absurde : contredit n0*)
                  destruct H8 as [_ [H8 _]]. rewrite H8 in *.
                  destruct (Hinv_pq src H H9).
                  - absurd (exists p : Path, is_path_from_to_restr G p pq src src); try tauto. exists [src]. simpl. tauto.
                  - destruct H11 as [p_ [_ [H11 H12]]].
                    specialize (H12 ([src]) ltac:(simpl; tauto)). simpl in H12.
                    destruct (nth src d None) eqn:Hn1; simpl in H12; try discriminate.
                    apply leb_complete in H12. replace n1 with 0 in * by lia.
                    pose proof (dist_decrease G d u src). simpl in H13. unfold get_dist in H13. rewrite Hdis, Hn1 in H13.
                    simpl in H13. apply leb_complete in H13. lia.
                }
                destruct (last_edge__ G p' pq' src u0 H10 H0 H8) as [p'' [v0 [H11 [H12 H13]]]]. simpl in H11.
                destruct H11 as [[H11 [H11' [[w0 H11_]]]]].
                rewrite <- Hdis in H7. rewrite (weight_add_vertex_end G p u0 u w H_cons (last_path_from_to G p pq src u ltac:(tauto)) H1) in H7. rewrite H7 in Hdis. rewrite <- Hdis.
                destruct (Nat.eq_dec v0 u).
                --(* v0 = u : p' fini par u *)
                  (* weigth p + w <= weigth p'' + w = weigth p' : on a besoin d'un intermédiaire restr entre p et p'' *)
                  rewrite e in *. rewrite H13.
                  destruct (cut_path_restr_u G d pq pq' p'' src u Hex H12) as [p0 [H16 H17]].
                  rewrite (weight_add_vertex_end G p'' u0 u w H_cons (last_path_from_to G p'' pq' src u H12) H1).
                  apply opt_le_siml_add'.
                  refine (opt_le_trans _ _ _ _ H17).
                  rewrite <- H5. apply H6. exact H16.
                --(* v0 <> u : p' fini pas par u *)
                  assert (~ In v0 pq). destruct (not_in_pq' _ _ _ _ v0 Hex ltac:(tauto)); tauto.
                  rewrite H13 in *.
                  (* weigth p + w = d[u] + w <= d[u0] (Hdis2) *)
                  rewrite <- H5. apply lt_impl_le in Hdis2. apply (opt_le_trans _ _ _ Hdis2). unfold get_dist.
                  destruct (Hinv_npq v0 ltac:(tauto) H16).
                  1:absurd (exists p : Path, is_path_from_to G p src v0); try tauto; exists p''; apply (rest_is_not_restr G p'' pq' src v0); assumption.
                  destruct H17. (* on a x optimal pour src -> v0 *)
                  (* d[u0] <= weigth x + w0 (Hinv_pq u0) <= weigth p'' + w0 (H17 : x opt parmis tous!!) *)
                  rewrite (weight_add_vertex_end G p'' u0 v0 w0 H_cons (last_path_from_to G p'' pq' src v0 H12) H11_).
                  apply (opt_le_trans _ (opt_add (path_weight' G x) (Some w0)) _).
                  +++destruct (Hinv_pq u0 H H9). (* on regarde le chemin optimal pour u0 *)
                    ---absurd (exists p : Path, is_path_from_to_restr G p pq src u0); try tauto.
                      exists (x++[u0]). apply (path_add_last_vertex _ _ v0); try tauto. exists w0; assumption.
                    ---rewrite <- (weight_add_vertex_end G x u0 v0 w0 H_cons (last_path_from_to G x pq src v0 ltac:(tauto)) H11_).
                      destruct H18 as [p1 [_ [_ H19]]]. apply H19. apply (path_add_last_vertex _ _ v0); try tauto. exists w0. assumption.
                  +++apply opt_le_siml_add'. destruct H17 as [_ [H17 H18]]. rewrite <- H17. apply H18. apply (rest_is_not_restr _ _ _ _ _ H12).
              }
        ++(* on a u -> u0 mais u est trop loin : améliore pas la distance : chemin opti inchangé *)
          pose proof (too_far_unchanged G d u u0 w H_cons H1 Hdis2). (* pour x, H1, Hdis2 -> d'[u0] = d[u0] *)
          pose proof (pq'_inc_pq _ _ _ _ _ Hex H0).
          destruct (Hinv_pq u0 H H3).
          1:destruct H4; rewrite H2 in Hdis; rewrite H5 in Hdis; discriminate.
          (* on a p0 opti pour u0 *)
          destruct H4 as [p0 [H4 [H5 H6]]]. exists p0. repeat split.
            **apply (restr_descrease_from_to _ _ _ _ _ _ _ _ Hex H4).
            **rewrite <- H5. rewrite H2 in Hdis. rewrite Hdis. reflexivity.
            **intros. rewrite H2 in Hdis.
              {
                (* **MONTRER QUE LE CHEMIN EST OPTIMAL** *)
                (* traiter le cas u0 = src à part *)
                destruct (Nat.eq_dec n 0). rewrite e. destruct (path_weight' G p'); reflexivity.
                assert (p' <> [u0]). { (* très similare à REP2 *)
                  intro. rewrite H8 in H7. simpl in H7.
                  (* mq u0 = src est absurde : contredit n0*)
                  destruct H7 as [_ [H7 _]]. rewrite H7 in *.
                  destruct (Hinv_pq src H H3).
                  - destruct H9. rewrite H10 in Hdis. discriminate.
                  - destruct H9 as [p_ [_ [H9 H10]]]. rewrite Hdis in H10.
                    specialize (H10 ([src]) ltac:(simpl; tauto)). simpl in H10.
                    apply leb_complete in H10. lia.
                }
                destruct (last_edge__ G p' pq' src u0 H8 H0 H7) as [p'' [v0 [H9 [H10 H11]]]]. simpl in H9.
                destruct (Nat.eq_dec v0 u).
                --(* v0 = u : p' fini par u *)
                  (* d[u0] = Some n (Hdis) <= d[u] + w (Hdis2) <= weigth p'' + w (H10, Hinv_pq : il faut assurer p'' restr pq !! si on a un u plus tot : on peut couper le chemin : couper : d[u] <= p''' (restr) <= p'') *)
                  rewrite e in *.
                  destruct (cut_path_restr_u G d pq pq' p'' src u Hex H10) as [p_ [H12 H12']].
                  destruct (Hinv_pq u ltac:(tauto) (u_in_pq _ _ _ _ Hex)).
                  1:absurd (exists p : Path, is_path_from_to_restr G p pq src u); try tauto; exists p_; assumption.
                  (* on a x opti pour src -> u *)
                  destruct H13. rewrite <- Hdis.
                  (* d[u0] <= d[u] + w (Hdis2) <= weigth H12 + w <= weigth p'' + w (H10, Hinv_pq) = weigth p' *)
                  apply rel_opt_le_lt in Hdis2. unfold get_dist in Hdis2. apply (opt_le_trans _ _ _ Hdis2).
                  rewrite H11, (weight_add_vertex_end G p'' u0 u w H_cons (last_path_from_to G p'' pq' src u ltac:(tauto)) H1).
                  apply opt_le_siml_add'. refine (opt_le_trans _ _ _ _ H12').
                  destruct H13 as [H13 [H14 H15]]. apply H15. assumption.
                --(* v0 <> u : p' fini pas par u *)
                  (* très similare à REP1 *)
                  assert (~ In v0 pq). destruct (not_in_pq' _ _ _ _ v0 Hex ltac:(tauto)); tauto.
                  destruct (Hinv_npq v0 ltac:(tauto) H12).
                  1:absurd (exists p : Path, is_path_from_to G p src v0); try tauto; exists p''; apply (rest_is_not_restr G p'' pq' src v0); assumption.
                  (* on a x optimal de src à v0 *)
                  destruct H13. rewrite <- Hdis.
                  (* (nth u0 d None) <= (par Hinv_pq) weigth x + w (de H8 : poids entre v0 et u0) <= p'' + w (par H12) = weigth p' (par H10) *)
                  pose proof (path_add_last_vertex G pq v0 u0 src x ltac:(tauto) H H12 ltac:(tauto)).
                  rewrite H11 in *.
                  (* (nth u0 d None) <= weigth H14 (Hinv_pq) = weigth x + w <= weigth p'' + w (H9, H13) = weigth H6 *)
                  destruct H9 as [[H9 [H9' [[w0 H9_]] ]]].
                  rewrite (weight_add_vertex_end G p'' u0 v0 w0 H_cons (last_path_from_to G p'' pq' src v0 H10) H9_).
                  apply (opt_le_trans _ (path_weight' G (x ++ [u0])) _ ltac:(apply H6; assumption)).
                  rewrite (weight_add_vertex_end G x u0 v0 w0 H_cons (last_path_from_to G x pq src v0 ltac:(tauto)) H9_).
                  apply opt_le_siml_add'.
                  destruct H13 as [_ [H13 H13']]. rewrite <- H13. apply H13'.
                  apply (rest_is_not_restr G p'' pq' src v0). assumption.
              }
      * (* non u->u0 donc d'[u0]=d[u0] unchanged : prendre le chemin de Hinv_pq *)
        rewrite (not_adj_unchanged G d u u0 H1) in Hdis.
        pose proof (pq'_inc_pq _ _ _ _ _ Hex H0).
        destruct (Hinv_pq u0 H H2).
        1:rewrite Hdis in H3; destruct H3; discriminate H4.
        (* p : chemin opti pour u0 : toujours opti *)
        destruct H3 as [p [H3 [H4 H5]]]. exists p.
        split. 1:apply (restr_descrease_from_to _ _ _ _ _ _ _ _ Hex H3).
        split. 1:(rewrite <- Hdis; exact H4).
        (* **MONTRER QUE LE CHEMIN EST OPTIMAL** *)
        intros.
        (* traiter le cas u0 = src à part *)
        destruct (Nat.eq_dec n 0). rewrite e. destruct (path_weight' G p'); reflexivity.
        assert (p' <> [u0]). { (* REP2 : H7 n0 Hinv_pq*)
          intro. rewrite H7 in H6. simpl in H6.
          (* mq u0 = src est absurde : contredit n0*)
          destruct H6 as [_ [H6 _]]. rewrite H6 in *.
          destruct (Hinv_pq src H H2).
          - destruct H8. rewrite H9 in Hdis. discriminate.
          - destruct H8 as [p_ [_ [H8 H9]]]. rewrite Hdis in H9.
            specialize (H9 ([src]) ltac:(simpl; tauto)). simpl in H9.
            apply leb_complete in H9. lia.
        }
        destruct (last_edge__ G p' pq' src u0 H7 H0 H6) as [p'' [v0 [H8 [H9 H10]]]]. simpl in H8.
        assert (v0 <> u). intro. rewrite H11 in H8. absurd (exists w : nat, In (u0, w) (nth u G [])); tauto.
        (* REP1 *)
        assert (~ In v0 pq). destruct (not_in_pq' _ _ _ _ v0 Hex ltac:(tauto)); tauto.
        destruct (Hinv_npq v0 ltac:(tauto) H12).
        1:absurd (exists p : Path, is_path_from_to G p src v0); try tauto; exists p''; apply (rest_is_not_restr G p'' pq' src v0); assumption.
        (* on a x optimal de src à v0 *)
        destruct H13. rewrite <- Hdis.
        (* (nth u0 d None) <= (par Hinv_pq) weigth x + w (de H8 : poids entre v0 et u0) <= p'' + w (par H12) = weigth p' (par H10) *)
        pose proof (path_add_last_vertex G pq v0 u0 src x ltac:(tauto) H H12 ltac:(tauto)).
        rewrite H10 in *.
        (* (nth u0 d None) <= weigth H14 (Hinv_pq) = weigth x + w <= weigth p'' + w (H9, H13) = weigth H6 *)
        destruct H8 as [[H8 [H8' [[w0 H8_]] ]]].
        rewrite (weight_add_vertex_end G p'' u0 v0 w0 H_cons (last_path_from_to G p'' pq' src v0 H9) H8_).
        apply (opt_le_trans _ (path_weight' G (x ++ [u0])) _ ltac:(apply H5; assumption)).
        rewrite (weight_add_vertex_end G x u0 v0 w0 H_cons (last_path_from_to G x pq src v0 ltac:(tauto)) H8_).
        apply opt_le_siml_add'.
        destruct H13 as [_ [H13 H13']]. rewrite <- H13. apply H13'.
        apply (rest_is_not_restr G p'' pq' src v0). assumption.
    + left. split; try reflexivity. intro. destruct H1.
      (* montrer que dist(u) est finie *)
      destruct (is_restr_cut G d _ pq pq' _ _ _ Hex H1).
      * (* on a un path restr : utiliser Hinv_pq *)
        destruct (Hinv_pq u0 H (pq'_inc_pq d pq pq' _ _ Hex H0)).
        1:absurd (exists p : Path, is_path_from_to_restr G p pq src u0); try tauto; exists x; assumption.
        destruct H3 as [p [H3 [H4 _]]].
        assert (nth u0 d None = None). pose proof (dist_decrease G d u u0). unfold get_dist in H5. rewrite Hdis in H5. destruct (nth u0 d None). try discriminate. reflexivity.
        destruct (is_path_from_to_restr_finite_weigth _ _ _ _ _ H_cons H3).
        rewrite H6 in H4. rewrite H5 in H4. discriminate.
      * destruct H2 as [_ [p' [_ H2]]].
        assert (exists n, nth u d None = Some n). {
          destruct (Hinv_pq u (last_restr_in_G _ _ _ _ _ H2) (u_in_pq _ _ _ _ Hex)).
          - absurd ((exists p : Path, is_path_from_to_restr G p pq src u)); try tauto. exists p'. assumption.
          - destruct H3 as [p [H3 [H4 _]]]. rewrite H4. apply (is_path_from_to_restr_finite_weigth _ _ _ _ _ H_cons H3).
        }
        (* monter que alors la relax va changer dist u0 *)
        (* disjonction sur le dernier sommet visité dans H1:
        - soit c'est u et on a u->u0, donc dist'(u0) <= dist(u)+w (et dist(u) = opt_restr et on a un chemin donc fini)
        - soit c'est pas u et c'est v -> u0. Mq src ->* v (sans passer par pq) par Hinv_npq : ca donnerait un src ->* u0 restrein : contredit Hinv_pq pour u0 (car d croit) *)
        assert (x <> [u0]). {
          (* mq u0 <> src... *)
          intro. rewrite H4 in H1.
          destruct (Hinv_pq u0 H (pq'_inc_pq _ _ _ _ _ Hex H0)).
          - absurd (exists p : Path, is_path_from_to_restr G p pq src u0); try tauto. exists [u0]. assumption.
          - destruct H5.
            assert (nth u0 d None = None). pose proof (dist_decrease G d u u0). unfold get_dist in H6. rewrite Hdis in H6. destruct (nth u0 d None). 1:discriminate. 1:reflexivity.
            rewrite H6 in H5. apply (is_path_from_to_restr_finite_weigth'' G x0 pq src u0); try tauto.
        }
        destruct (last_edge_ G x pq' src u0 H4 H0 H1) as [p_ [v0 [H5 H_path_v0]]].
        destruct (Nat.eq_dec v0 u).
        **rewrite e in H5. destruct H3. destruct H5 as [[_ [_ [[w H5] _]]] _].
          (*In (u0, w) (nth u G []) -> opt_le (nth u d None) (nth u0 d' None) = true*)
          (*nth u d None = Some x0 -> In (u0, w) (nth u G []) -> exists x1, nth u0 d' None = Some x1*)
          destruct (adj_d'_smaller' G d u u0 x0 w H Hinv_ H_cons H3 H5).
          rewrite H6 in Hdis. discriminate Hdis.
        **destruct H5 as [H5 _]. simpl in H5.
          (* on a v -> u0. par Hinv_npq, on a src ->* v (sans passer par pq).
            ca donne src ->* u0 restrein.
            contredit Hinv_pq pour u0 (car d croit) *)
          assert (~ In v0 pq). apply (not_in_pq' _ _ _ _ v0) in Hex; tauto.
          destruct (Hinv_npq v0 ltac:(tauto) H6).
          ++absurd (exists p : Path, is_path_from_to G p src v0); try tauto.
            exists p_. assumption.
          ++absurd (exists p : Path, is_path_from_to_restr G p pq src u0).
           +++destruct (Hinv_pq u0 H (pq'_inc_pq _ _ _ _ _ Hex H0)); try tauto.
              (* H8 et Hdis + d croissante : dist = None pour un chemin *)
              pose proof (dist_decrease G d u u0). unfold get_dist in H9. rewrite Hdis in H9.
              destruct (nth u0 d None); try discriminate H9. destruct H8 as [x0 [H8 H8_]].
              apply (path_from_to_rest_weigth) in H8; try tauto.
           +++destruct H7 as [x0 [H7 _]]. exists (x0++[u0]). apply (path_add_last_vertex G pq v0 u0 src x0); tauto.
  - rewrite Hinv_. rewrite lengthd_eq_length_d'. reflexivity.
Qed.

Lemma all_step_preserves_invariant :
  forall G (H_cons: consistent_weigth G) src n pq d,
    length pq <= n ->
    dijkstra_invariant G H_cons src pq d ->
    dijkstra_invariant G H_cons src [] (dijkstra_loop G pq d).
Proof.
  intros G H_cons src n.
  induction n; intros.
  - assert (length pq = 0). lia.
    apply length_zero_iff_nil in H1.
    assert (dijkstra_loop G [] d = d). rewrite dijkstra_loop_equation. reflexivity.
    rewrite H1 in *. rewrite H2. assumption.
  - destruct pq.
    * assert (dijkstra_loop G [] d = d). rewrite dijkstra_loop_equation. reflexivity.
      rewrite H1. assumption.
    * assert (exists u pq', extract_min (n0 :: pq) d = Some (u, pq')). apply extract_min_empty. intro. discriminate.
    destruct H1 as [u [pq' H1]].
    rewrite dijkstra_loop_equation. rewrite H1.
    set (d' := fold_left (fun acc '(v,w) => relax acc u v w) (neighbors G u) d).
    apply (IHn pq' d').
    + assert (length pq' < length (n0::pq)). {
      unfold extract_min in H1.
      replace pq' with (remove Nat.eq_dec (argmin_nonempty d n0 pq) (n0 :: pq)).
      apply remove_length_lt. apply argmin_nonempty_correct.
      inversion H1. simpl. destruct (Nat.eq_dec (argmin_nonempty d n0 pq) n0); reflexivity.
    }
    simpl in *. lia.
    + apply (step_preserves_invariant G H_cons src _ d u pq' H0 H1).
Qed.

Theorem dijkstra_correct (G:Graph) (H_cons: consistent_weigth G) (src:nat) (H_non_empty: vertex_is_in G src):
  let d := dijkstra G src in forall u, vertex_is_in G u -> minimum_dist_from_to G (nth u d None) src u H_cons.
Proof.
  simpl. unfold dijkstra. intros. unfold minimum_dist_from_to.
  assert (exists u pq', extract_min (init_pq (length G)) (init_dist (length G) src) = Some (u, pq')).
  {
    apply extract_min_empty. destruct (length G) eqn:l.
    - unfold vertex_is_in in H_non_empty. rewrite l in H_non_empty. lia.
    - simpl. discriminate.
  }
  destruct H0 as [u' [pq' H0]].
  pose proof (dijkstra_init_invariant G H_cons src u' pq' H0). simpl in H1.
  pose proof (all_step_preserves_invariant G H_cons src (length (init_pq (length G)))). apply H2 in H1; try reflexivity.
  destruct H1 as [H1 _]. specialize (H1 u H ltac:(intro; contradiction)).
  destruct H1 as [H1 | H1]; try tauto.
  right. destruct H1. exists x. repeat split; try tauto.
  destruct H1 as [H1 _]. apply rest_is_not_restr in H1. assumption.
Qed.



(* si src et dest sont connexes, alors il existe un chemin qui est minimal et dont la distance est renvoyée par dijkstra *)
Proposition dijkstra_correct' (G:Graph) (H_cons: consistent_weigth G) (src dest: nat):
  vertex_is_in G src -> vertex_is_in G dest ->
  (exists (p:Path), is_path_from_to G p src dest) ->
  exists (p:Path) (H_path: is_path_from_to G p src dest),
    path_weight' G p = get_dist (dijkstra G src) dest /\
    minimum_path_from_to G p src dest H_cons H_path.
Proof.
  intros. pose proof (dijkstra_correct G H_cons src H dest H0).
  destruct H2; try tauto. destruct H2 as [p [Hp [H2 H3]]].
  unfold get_dist, minimum_path_from_to. exists p, Hp. split.
  - rewrite H2. reflexivity.
  - intros. specialize (H3 p' H_p'). rewrite H2 in H3.
    rewrite (path_weigth_equiv_2 G p H_cons (path_equiv_2 G p H_cons (is_path_from_to_IS_A_PATH G p src dest Hp))) in H3.
    rewrite (path_weigth_equiv_2 G p' H_cons (path_equiv_2 G p' H_cons (is_path_from_to_IS_A_PATH G p' src dest H_p'))) in H3.
    simpl in H3. apply leb_complete. assumption.
Qed.

Proposition dijkstra_correct'' (G:Graph) (H_cons: consistent_weigth G) (src dest: nat) (p:Path) (H_path:is_path_from_to G p src dest):
  minimum_path_from_to G p src dest H_cons H_path ->
  path_weight' G p = get_dist (dijkstra G src) dest.
Proof.
  destruct (ext_in_G G p src dest H_path) as [H0 H].
  destruct (dijkstra_correct' G H_cons src dest H H0 ltac:(exists p; exact H_path)) as [p'[H_path'[H1 H2]]].
  intro. rewrite <- H1. unfold minimum_path_from_to in *.
  rewrite (path_weigth_equiv_2 G p H_cons (path_equiv_2 G p H_cons (is_path_from_to_IS_A_PATH G p src dest H_path))).
  rewrite (path_weigth_equiv_2 G p' H_cons (path_equiv_2 G p' H_cons (is_path_from_to_IS_A_PATH G p' src dest H_path'))).
  specialize (H2 p H_path). specialize (H3 p' H_path'). f_equal. lia.
Qed.

