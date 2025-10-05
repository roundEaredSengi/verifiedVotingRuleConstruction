section \<open>Voting Power\<close>

theory Voting_Power
  imports Voting_Models
          Distance
          "HOL-Probability.Probability_Measure"

begin

subsection \<open>Auxiliary Lemmas and Definitions\<close>

fun uncurry3 :: "('w \<Rightarrow> 'x \<Rightarrow> 'y \<Rightarrow> 'z) \<Rightarrow> (('w \<times> 'x \<times> 'y) \<Rightarrow> 'z)" where
  "uncurry3 f = (\<lambda>(w,x,y). f w x y)"

fun swap_voters :: "'v \<Rightarrow> 'v \<Rightarrow> ('a, 'v) Election \<Rightarrow> ('a, 'v) Election" where
  "swap_voters v w e = 
    (let \<pi> = (\<lambda>x::'v. (if x = w then v else (if x = v then w else x))) in
      rename \<pi> e)"

fun coincide_except :: "('a, 'v) Election \<Rightarrow> ('a, 'v) Election \<Rightarrow> 'v \<Rightarrow> bool" where
  "coincide_except e1 e2 v = 
      (\<forall> w \<in> (voters_\<E> e1) - {v}. profile_\<E> e1 w = profile_\<E> e2 w)"

lemma rename_inv_commute:
  fixes
    \<pi> :: "'v \<Rightarrow> 'v"
  assumes "bij \<pi>"
  shows
    "the_inv (rename \<pi>) = rename (the_inv \<pi>)"
proof -
  have "(rename (the_inv \<pi>)) \<circ> (rename \<pi>) = id"
    unfolding comp_def
    using rename_inv ext assms id_def inj_def prod_cases3 rename_inj
    by (metis (no_types, lifting))
  thus "the_inv (rename \<pi>) = rename (the_inv \<pi>)"
    using  ext assms bij_betw_the_inv_into comp_apply id_apply rename_inj the_inv_f_f
    by (metis (no_types, lifting))
qed

lemma card_orders: 
  fixes
    X :: "'x set"
  shows "finite X \<Longrightarrow> card {rel. linear_order_on X rel} = fact (card X)"
proof (induction "card X" arbitrary: X)
  case 0
  fix 
    X :: "'x set"
  assume 
    0: "0 = card X" and
    "finite X"
  hence "X = {}"
    by simp
  hence "Collect (linear_order_on X) = {{}}"
    unfolding linear_order_on_def partial_order_on_def total_on_def 
              preorder_on_def antisym_def refl_on_def trans_def
    by blast
  thus "card (Collect (linear_order_on X)) = fact (card X)"
    using 0
    by simp
next
  case (Suc x)
  fix 
    x :: nat and
    X :: "'x set"
  assume
    fin: "finite X" and
    card: "Suc x = card X" and
    hyp: 
      "\<And>(X::'x set). x = card X \<Longrightarrow> finite X \<Longrightarrow> 
                      card (Collect (linear_order_on X)) = fact (card X)"
  have "Suc x > 0"
    by blast
  hence "card X \<noteq> 0"
    using card
    by simp
  moreover have "card {} = 0"
    by simp
  ultimately have "X \<noteq> {}"
    by blast
  then obtain z :: 'x where "z \<in> X"
    by blast
  let ?Xm = "X - {z}"
  have "x = card ?Xm"
    using card
    by (simp add: \<open>z \<in> X\<close>)
  moreover have "finite ?Xm"
    using fin
    by blast
  ultimately have cardm: "card (Collect (linear_order_on ?Xm)) = fact (card ?Xm)"
    using hyp[of "?Xm"] card_partition
    by blast
  let ?extOrd = "\<lambda>p. {pi. linear_order_on X pi \<and> (pi \<inter> (?Xm \<times> ?Xm)) = p}"
  let ?ords = "{?extOrd p | p. p \<in> Collect (linear_order_on ?Xm)}"
  let ?rk = "\<lambda>x rel. card {y. (y, x) \<in> rel}"
  let ?f = "\<lambda>pi. ?rk z pi"
  have inj: "\<forall>p \<in> Collect (linear_order_on ?Xm). inj_on ?f (?extOrd p)"
    unfolding inj_on_def 
    sorry
  moreover have "\<forall>p \<in> Collect (linear_order_on ?Xm). ?f ` (?extOrd p) = {1..card X}"
    sorry
  ultimately have "\<forall>p \<in> Collect (linear_order_on ?Xm). bij_betw ?f (?extOrd p) {1..card X}"
    sorry
  hence "\<forall>p \<in> Collect (linear_order_on ?Xm). card (?extOrd p) = card {1..card X}"
    using bij_betw_same_card
    by blast
  moreover have "card {1..card X} = card X"
    using atLeast0LessThan card_lessThan 
    by simp
  ultimately have eltCard0: "\<forall>p \<in> Collect (linear_order_on ?Xm). card (?extOrd p) = card X"
    by simp
  hence eltCard:
    "\<forall> pi \<in> {?extOrd p |p. p \<in> Collect (linear_order_on (X - {z}))}. card pi = card X"
    by blast
  have 
    "\<forall>p1 \<in> Collect (linear_order_on ?Xm). \<forall>p2 \<in> Collect (linear_order_on ?Xm).
          p1 \<noteq> p2 \<longrightarrow> 
            (\<forall>pi1 \<in> (?extOrd p1). \<forall>pi2 \<in> (?extOrd p2). 
              (pi1 \<inter> (?Xm \<times> ?Xm)) \<noteq> (pi2 \<inter> (?Xm \<times> ?Xm)))"
    by simp
  hence disj0:
    "\<forall>p1 \<in> Collect (linear_order_on ?Xm). \<forall>p2 \<in> Collect (linear_order_on ?Xm).
        p1 \<noteq> p2 \<longrightarrow> ?extOrd p1 \<inter> ?extOrd p2 = {}"
    by blast
  hence disj:
    "\<forall> pi1 \<in> {?extOrd p |p. p \<in> Collect (linear_order_on (X - {z}))}.
      \<forall> pi2 \<in> {?extOrd p |p. p \<in> Collect (linear_order_on (X - {z}))}.
        pi1 \<noteq> pi2 \<longrightarrow> pi1 \<inter> pi2 = {}"
    by blast
  have "\<forall>p \<in> Collect (linear_order_on ?Xm). 
    (\<exists>pi. linear_order_on X pi \<and> (pi \<inter> ?Xm \<times> ?Xm) = p)"
    using eltCard0 \<open>card X \<noteq> 0\<close>
    by (metis (mono_tags, lifting) Collect_empty_eq card_eq_0_iff)
  hence "\<forall>p \<in> Collect (linear_order_on ?Xm). ?extOrd p \<noteq> {}"
    by simp
  hence "inj_on ?extOrd (Collect (linear_order_on ?Xm))"
    using disj0
    unfolding inj_on_def
    by (metis (lifting) inf.idem)
  moreover have "?extOrd ` (Collect (linear_order_on ?Xm)) = ?ords"
    by blast
  ultimately have "bij_betw ?extOrd (Collect (linear_order_on ?Xm)) ?ords"
    unfolding bij_betw_def
    by blast
  hence cardIndex: "card ?ords = card (Collect (linear_order_on ?Xm))"
    by (simp add: bij_betw_same_card)
  have "finite (Collect (linear_order_on ?Xm))"
    by (metis card.infinite cardm fact_nonzero)
  hence fin: "finite ?ords"
    by simp
  moreover have "\<forall>p \<in> Collect (linear_order_on ?Xm). finite (?extOrd p)"
    using \<open>card X \<noteq> 0\<close> card_eq_0_iff eltCard0 
    by force
  ultimately have finU: "finite (\<Union>?ords)"
    by blast
  have cardU: "card (\<Union>?ords) = (card X) * (fact (card ?Xm))"
    using eltCard card_partition[of ?ords "card X"] cardm disj fin finU cardIndex
    by simp
  have "\<forall>p. linear_order_on X p \<longrightarrow> linear_order_on ?Xm (p \<inter> (?Xm \<times> ?Xm))"
    unfolding linear_order_on_def partial_order_on_def total_on_def 
              preorder_on_def refl_on_def trans_def antisym_def 
    by blast
  moreover have "\<forall>p. linear_order_on X p \<longrightarrow> p \<in> ?extOrd (p \<inter> (?Xm \<times> ?Xm))"
    by simp
  ultimately have "Collect (linear_order_on X) \<subseteq> \<Union>?ords"
    by blast
  moreover have "\<Union>?ords \<subseteq> Collect (linear_order_on X)"
    by blast
  ultimately have "\<Union>?ords = Collect (linear_order_on X)"
    by blast
  hence "card (Collect (linear_order_on X)) = (card X) * (fact (card ?Xm))"
    using cardU
    by simp
  also have "(card X) * (fact (card ?Xm)) = fact (card X)"
    using \<open>x = card ?Xm\<close> card fact_Suc id_apply of_nat_eq_id
    by metis
  finally show "card (Collect (linear_order_on X)) = fact (card X)"
    by argo
qed

subsection \<open>Voting Power\<close>

type_synonym ('v, 'x) Voting_Power = "'x \<Rightarrow> 'v \<Rightarrow> real"

record ('v, 'x) abstract_notions =
  has_swing_vote :: "'x \<Rightarrow> 'v \<Rightarrow> bool"
  rename_instance :: "('v \<Rightarrow> 'v) \<Rightarrow> 'x \<Rightarrow> 'x"

locale voting_power = voting_model \<V> \<M>
  for \<V> :: "'v set" and \<M> :: "'x set" +
  fixes
    \<delta> :: "('v, 'x) Voting_Power" and
    AN :: "('v, 'x) abstract_notions" (structure) 
begin

subsection \<open>(Abstract) Voting Power Axioms\<close>

definition null_player :: "bool" where
  "null_player = (\<forall> m \<in> \<M>. \<forall> v \<in> \<V>. \<not>(has_swing_vote AN m v) \<longrightarrow> \<delta> m v = 0)"

definition non_negativity :: "bool" where
  "non_negativity = (\<forall> m \<in> \<M>. \<forall> v \<in> \<V>. \<delta> m v \<ge> 0)"

definition symmetry :: "bool" where
  "symmetry = (\<forall> \<pi> \<in> Bij \<V>. \<forall> m \<in> \<M>. \<forall> v \<in> \<V>. \<delta> m v = \<delta> (rename_instance AN \<pi> m) (\<pi> v))"
  (* TODO relate with is_symmetry def *)

end

subsection \<open>Specific Voting Power Indices\<close>

locale banzhaf_index = voting_power \<V> \<M> \<delta> 
  for \<V> :: "'v set" and \<M> :: "'x set" and \<delta> :: "('v, 'x) Voting_Power" +
  fixes
    banzhaf_count :: "'x \<Rightarrow> 'v \<Rightarrow> nat"
  assumes
    "null_player" and "symmetry" and "non_negativity"
    "TRUE" (* TODO *)
begin
  
end
  
subsection \<open>Equivalence of Voting Power Indices Defined on Different Models\<close>

locale power_equivalence = 
  model_isomorphism \<V> \<M> \<M>' isom + 
  v1: voting_power \<V> \<M> \<delta> AN + 
  v2: voting_power \<V> \<M>' \<delta>' AN'
  for \<V> :: "'v set" and \<M> :: "'x set" and \<M>' :: "'y set" and isom :: "'x \<Rightarrow> 'y \<Rightarrow> bool"
    and AN :: "('v, 'x) abstract_notions" and AN' :: "('v, 'y) abstract_notions"
    and \<delta> :: "('v, 'x) Voting_Power" and \<delta>' :: "('v, 'y) Voting_Power" +
  assumes
    coincide: "\<forall> m \<in> \<M>. \<forall> m' \<in> \<M>'. \<forall> v \<in> \<V>. isom m m' \<longrightarrow> \<delta> m v = \<delta>' m' v"

context model_comparison
begin

fun equiv_pow_props :: 
  "(('v, 'x) Voting_Power \<Rightarrow> bool) \<Rightarrow> (('v, 'y) Voting_Power \<Rightarrow> bool) \<Rightarrow> bool" where
  "equiv_pow_props \<phi> \<phi>' = 
    (\<forall> \<delta> \<delta>'. (power_equivalence \<V> \<M> \<M>' isomorphic \<delta> \<delta>') \<longrightarrow> (\<phi> \<delta> \<longleftrightarrow> \<phi>' \<delta>'))"

end

subsection \<open>(Temporary) Dump\<close>

end

(*

type_synonym ('a, 'v, 'r) Swing_Weight =
  "('a, 'v, 'r) Electoral_Module \<Rightarrow> ('a, 'v) Election \<Rightarrow> 'v \<Rightarrow> ereal"

text \<open>
  A voting power index is defined on tuples of voting rules (electoral modules) and voters. 
  The domain of a voting rule (those ballot configurations relevant to the power index) 
  is not necessarily the complete Election type universe, so it is instead given as another 
  input in this implementation.
\<close>
type_synonym ('a, 'v, 'r) Voting_Power_Domain =
  "('a, 'v, 'r) Electoral_Module \<times> ('a, 'v) Election set \<times> 'v"

type_synonym ('a, 'v, 'r) Uncurried_Voting_Power =
  "('a, 'v, 'r) Voting_Power_Domain \<Rightarrow> ereal"

fun rule :: "('a, 'v, 'r) Voting_Power_Domain \<Rightarrow> ('a, 'v, 'r) Electoral_Module" where
  "rule X = fst X"

fun counting_domain :: "('a, 'v, 'r) Voting_Power_Domain \<Rightarrow> ('a, 'v) Election set" where
  "counting_domain X = fst (snd X)"

fun voter :: "('a, 'v, 'r) Voting_Power_Domain \<Rightarrow> 'v" where
  "voter X = snd (snd X)"

subsection \<open>Abstract Voting Power Indices (Locale)\<close>

type_synonym ('a, 'v, 'r) Voting_Power_Axiom = 
  "('a, 'v, 'r) Uncurried_Voting_Power \<Rightarrow> ('a, 'v, 'r) Voting_Power_Domain set \<Rightarrow> bool"

(* TODO define VP axioms outside of the locale in a manner that takes voting power index + domain
as input instead of as parameters? Either that or change the Extension.thy structure completely *)

subsection \<open>Symmetry of Abstract Voting Power Measures\<close>

fun rename_rule :: 
  "('v \<Rightarrow> 'v) \<Rightarrow> ('a, 'v, 'r) Electoral_Module \<Rightarrow> ('a, 'v, 'r) Electoral_Module" where
  "rename_rule \<pi> f = (\<lambda> V A p. (fun\<^sub>\<E> f) ((the_inv (rename \<pi>)) (A, V, p)))"

fun rename_pow :: 
  "('v \<Rightarrow> 'v) \<Rightarrow> (('a, 'v, 'r) Voting_Power_Domain \<Rightarrow> ('a, 'v, 'r) Voting_Power_Domain)" where
  "rename_pow \<pi> (f, E, v) = (rename_rule \<pi> f, (rename \<pi>) ` E, \<pi> v)"

subsection \<open>I-Power Interpretation of Abstract Voting Power Measures\<close>

(* definition ipower :: 
  "(('a, 'v, 'r) Voting_Power_Domain \<Rightarrow> ('a, 'v) Election measure) \<Rightarrow>
    (('a, 'v, 'r) Voting_Power_Domain \<Rightarrow> ('a, 'v) Election set) \<Rightarrow> 
      bool" 
  where 
    "ipower M event = (\<forall> X \<in> domain. prob_space (M X) \<and>
      \<delta> (rule X) (counting_domain X) (voter X) = (emeasure (M X)) (event X))" *)

subsection \<open>Relations between Voting Power and other Axiomatic Properties\<close>

lemma anon_rule_imp_symmetry_pow_const:
  fixes
    f :: "('a, 'v, 'r) Electoral_Module" and
    E :: "('a, 'v) Election set" and
    v :: 'v and
    w :: 'v 
  assumes 
    sym_pow: "pow_symmetry" and
    anon_rule: "anonymity_in E f" and
    well_formed_counting_domain: "swap_voters v w ` E  = E" and
    domain_constrained_delta: 
      "\<forall> f g Y x. (\<forall> e \<in> Y. 
        f (voters_\<E> e) (alternatives_\<E> e) (profile_\<E> e) = 
        g (voters_\<E> e) (alternatives_\<E> e) (profile_\<E> e))
        \<longrightarrow> \<delta> f Y x = \<delta> g Y x" and
    valid_v: "(f, E, v) \<in> domain" and
     well_formed_counting_domain': 
      "rename_pow (\<lambda> x :: 'v. (if x = w then v else (if x = v then w else x))) (f, E, v) \<in> domain"
  shows "\<delta> f E v = \<delta> f E w"
proof -
  (* Generally, the symmetric power of v under f, E equals that of pi(v) under f_pi, pi(E). *)
  let ?\<pi> = "(\<lambda> x :: 'v. (if x = w then v else (if x = v then w else x)))"
  have bij0: "bij ?\<pi> \<and> bij (the_inv ?\<pi>)"
    by (simp add: bij_betw_the_inv_into involuntory_imp_bij)
  hence bij: "?\<pi> \<in> Bij UNIV \<and> (the_inv ?\<pi>) \<in> Bij UNIV"
    unfolding Bij_def extensional_def
    by simp
  moreover have 
    "((rename_rule ?\<pi> f), ((rename ?\<pi>) ` E), (?\<pi> v)) = rename_pow ?\<pi> (f, E, v)"
    by simp
  ultimately have 
    "\<exists> x \<in> Bij UNIV. 
      rename_pow x (f, E, v) = ((rename_rule ?\<pi> f), ((rename ?\<pi>) ` E), (?\<pi> v))"
    using valid_v
    by metis
  hence
    "((f, E, v), ((rename_rule ?\<pi> f), ((rename ?\<pi>) ` E), (?\<pi> v))) \<in> 
      action_induced_rel (Bij (UNIV::('v set))) domain (\<lambda> \<pi>. rename_pow \<pi>)"
    using valid_v
    by simp
  moreover have "((f, E, v), ((rename_rule ?\<pi> f), ((rename ?\<pi>) ` E), (?\<pi> v))) \<in> domain \<times> domain"
    using  well_formed_counting_domain' valid_v
    unfolding rename_pow.simps
    by blast
  ultimately have eq0: "\<delta> f E v = \<delta> (rename_rule ?\<pi> f) ((rename ?\<pi>) ` E) (?\<pi> v)"
    using sym_pow
    unfolding pow_symmetry_def is_symmetry.simps
    by simp
  (* pi(v) = w, E_pi = E and f_pi = f (constrained to E) yields the result 
    given that delta does not care about values of f outside of E. *)
  have 
    "\<forall> e \<in> E. extensional_continuation (the_inv (rename ?\<pi>)) E e = (the_inv (rename ?\<pi>)) e"
    by simp
  hence 
    "\<forall> e \<in> E. \<exists> x \<in> Bij UNIV. 
      extensional_continuation (the_inv (rename ?\<pi>)) E e = 
      (the_inv (rename ?\<pi>)) e"
    using bij id_Bij
    unfolding \<phi>_anon.simps
    by blast
  hence "\<forall> e \<in> E. \<exists> x \<in> Bij UNIV. \<phi>_anon E x e = (the_inv (rename ?\<pi>)) e"
    unfolding \<phi>_anon.simps
    using rename_inv_commute
    by (metis (no_types, lifting) bij0 bij)
  hence "\<forall> e \<in> E. (e, (the_inv (rename ?\<pi>)) e) \<in> anonymity\<^sub>\<R> E"
    using bij
    unfolding anonymity\<^sub>\<R>.simps action_induced_rel.simps bijection\<^sub>\<V>\<^sub>\<G>_def BijGroup_def
    by simp
  hence
    "\<forall> e \<in> E. rename_rule ?\<pi> f (voters_\<E> e) (alternatives_\<E> e) (profile_\<E> e) = 
                f (voters_\<E> e) (alternatives_\<E> e) (profile_\<E> e)"
    using anon_rule alternatives_\<E>.elims prod.collapse profile_\<E>.elims voters_\<E>.elims
    unfolding anonymity_in.simps is_symmetry.simps fun\<^sub>\<E>.simps rename_rule.simps
    by (metis (lifting))
  hence "\<delta> f E w = \<delta> (rename_rule ?\<pi> f) E w"
    using domain_constrained_delta
    by presburger
  moreover have "w = ?\<pi> v"
    by simp
  moreover have "E = (rename ?\<pi>) ` E"
    using well_formed_counting_domain
    by simp
  ultimately have "\<delta> f E w = \<delta> (rename_rule ?\<pi> f) ((rename ?\<pi>) ` E) (?\<pi> v)"
    by simp
  thus "\<delta> f E v = \<delta> f E w"
    using eq0
    by simp
qed

subsection \<open>Characteristics of Specific Power Indices (Sublocales)\<close>

definition uniform_elections :: "('b, 'a, 'c) Voting_Power_Domain \<Rightarrow> ('b, 'a) Election measure"
  where "uniform_elections X = uniform_count_measure (counting_domain X)"

locale banzhaf_index = voting_power_measure +
  fixes
    swing_vote :: "('b, 'a, 'c) Voting_Power_Domain \<Rightarrow> ('b, 'a) Election set"
  assumes 
    sym: "pow_symmetry" and
    prob: "ipower uniform_elections swing_vote"
    (* and TODO *)
begin

(* TODO *)

end
 
sublocale banzhaf_index \<subseteq> voting_power_measure
proof - qed

subsection \<open>Concrete Voting Power Indices (Locale Instantiations)\<close>

(* classical swing votes *)
fun swing_votes :: 
  "('a, 'v, 'r) Electoral_Module \<Rightarrow> ('a, 'v) Election set \<Rightarrow> 'v \<Rightarrow> (('a, 'v) Election) rel" where
  "swing_votes f E v = {(e1, e2) \<in> E \<times> E. 
      fun\<^sub>\<E> f e1 \<noteq> fun\<^sub>\<E> f e2 \<and> voters_\<E> e1 = voters_\<E> e2 \<and> coincide_except e1 e2 v}"

subsubsection \<open>Voting Power Indices Defined on a Fixed Voter and Alternative Set\<close>

locale fixed_elections =
  fixes
    V :: "'v set" and
    A :: "'a set"
  assumes
    finVot: "finite V" and
    finAlt: "finite A"
begin

definition elec :: "('a, 'v) Election set" where
  "elec = {(A, V, restrict p V) | p. profile V A p}"

fun left :: "'x rel \<Rightarrow> 'x set" where
  "left rel = {x. (\<exists>y. (x, y) \<in> rel)}"

fun banzhaf_swing :: "('a, 'v, 'r) Voting_Power_Domain \<Rightarrow> ('a, 'v) Election set" where
  "banzhaf_swing X = left (swing_votes (rule X) (counting_domain X) (voter X))"

fun banzhaf_count :: "('a, 'v, 'r) Voting_Power" where
  "banzhaf_count f E v = (1/((card E)::real)) * (card (banzhaf_swing (f, E, v)))"

definition elec_domain :: "('a, 'v, 'r) Voting_Power_Domain set" where
  "elec_domain = {X. counting_domain X = elec \<and> voter X \<in> V}"

lemma card_elec: "card elec = (fact (card A))^(card V)"
proof -
  let ?f = "\<lambda> p::(('a, 'v) Profile). (A, V, p)"
  have "\<forall> A' V' p. A' = A \<and> V' = V \<longrightarrow> (A', V', p) = ?f p"
    by meson
  hence "?f ` {restrict p V | p. profile V A p} = elec"
    unfolding elec_def
    by blast
  moreover have "inj_on ?f {restrict p V | p. profile V A p}"
    unfolding inj_on_def
    by simp
  ultimately have "bij_betw ?f {restrict p V | p. profile V A p} elec"
    unfolding bij_betw_def
    by blast
  hence "card elec = card {restrict p V | p. profile V A p}"
    by (simp add: bij_betw_same_card elec_def)
  also have "card {restrict p V | p. profile V A p} = (fact (card A))^(card V)"
  proof -
    have 
      "\<forall>f. f \<in> {restrict p V | p. profile V A p} \<longrightarrow> f \<in> V \<rightarrow>\<^sub>E {rel. linear_order_on A rel}"
      using restrict_PiE[of _ V "\<lambda> x. Collect (linear_order_on A)"]
      unfolding profile_def extensional_def PiE_def Pi_def
      by blast
    hence subset1: "{restrict p V | p. profile V A p} \<subseteq> (V \<rightarrow>\<^sub>E {rel. linear_order_on A rel})"
      by blast
    have
      "\<forall>f. f \<in> V \<rightarrow>\<^sub>E {rel. linear_order_on A rel} \<longrightarrow>
          f \<in> {f. \<forall>x. x \<in> V \<longrightarrow> f x \<in> Collect (linear_order_on A)}"
      by blast 
    moreover have
      "\<forall>f. f \<in> {f. \<forall>x. x \<in> V \<longrightarrow> f x \<in> Collect (linear_order_on A)}
          \<longrightarrow> restrict f V \<in> {restrict p V | p. profile V A p}"
      using restrict_PiE[of _ V "\<lambda> x. Collect (linear_order_on A)"] 
      unfolding profile_def
      by blast
    ultimately have 
      "\<forall>f. f \<in> V \<rightarrow>\<^sub>E {rel. linear_order_on A rel} \<longrightarrow> f \<in> {restrict p V | p. profile V A p}"
      using PiE_restrict[of _ V "\<lambda> x. Collect (linear_order_on A)"] 
      unfolding PiE_def extensional_def
      by (metis (no_types, lifting))
    hence subset2: "(V \<rightarrow>\<^sub>E {rel. linear_order_on A rel}) \<subseteq> {restrict p V | p. profile V A p}"
      by blast
    from subset1 subset2 have
      "{restrict p V | p. profile V A p} = (V \<rightarrow>\<^sub>E {rel. linear_order_on A rel})"
      by blast
    hence 
      "card {restrict p V | p. profile V A p} = card (V \<rightarrow>\<^sub>E {rel. linear_order_on A rel})"
      by simp
    also have 
      "card (V \<rightarrow>\<^sub>E {rel. linear_order_on A rel}) = (card {rel. linear_order_on A rel}) ^ (card V)"
      using card_funcsetE finVot
      by blast
    also have "(card {rel. linear_order_on A rel}) ^ (card V) = (fact (card A)) ^ (card V)"
      using card_orders finAlt
      by metis
    finally show ?thesis
      by simp
  qed
  finally show ?thesis
    by blast
qed

lemma card_elec_ge_0: "card elec > 0"
proof -
  have "0 < ((fact (card A))::nat)"
    using fact_gt_zero
    by blast
  hence "((fact (card A))::nat)^(card V) > 0"
    using Power.linordered_semidom_class.zero_less_power
    by blast
  moreover have "card elec = (fact (card A))^(card V)"
    using card_elec
    by blast
  ultimately show ?thesis
    using elec_def
    by simp
qed

lemma non_empty: "elec \<noteq> {}"
  proof -
    have "elec = {} \<Longrightarrow> card elec = 0"
      by simp
    moreover have "card elec \<noteq> 0"
      using card_elec_ge_0
      by simp
    ultimately show ?thesis
      by blast
  qed

lemma finite: "finite elec"
  using card_elec_ge_0 card_ge_0_finite
  by blast

lemma rename_roundtrip:
  fixes
    e :: "('a, 'v) Election" and
    f :: "('a, 'v, 'r) Electoral_Module" and
    \<pi> :: "'v \<Rightarrow> 'v"
  assumes
    "bij \<pi>"
  shows
    "fun\<^sub>\<E> f e = fun\<^sub>\<E> (voting_power_measure.rename_rule \<pi> f) (rename \<pi> e)"
proof -
  have "fun\<^sub>\<E> (voting_power_measure.rename_rule \<pi> f) (rename \<pi> e) = 
        fun\<^sub>\<E> f (the_inv (rename \<pi>) (rename \<pi> e))"
    unfolding voting_power_measure.rename_rule.simps
    by simp
  also have "fun\<^sub>\<E> f (the_inv (rename \<pi>) (rename \<pi> e)) = fun\<^sub>\<E> f e"
    using assms
    by (simp add: rename_inj the_inv_f_f)
  finally show ?thesis
    by simp
qed

lemma rename_presv_swing:
  fixes
      f :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('v \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> 'c" and
      E :: "('a, 'v) Election set" and
      v :: 'v and
      g :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('v \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> 'c" and
      F :: "('a, 'v) Election set" and
      w :: 'v and
      \<pi> :: "'v \<Rightarrow> 'v"
    assumes
      valid: "(f, E, v) \<in> elec_domain" and
      valid': "(g, F, w) \<in> elec_domain" and
      bij: "\<pi> \<in> Bij UNIV" and
      re: "voting_power_measure.rename_pow \<pi> (f, E, v) = (g, F, w)"
    shows
      "(rename \<pi>) ` (banzhaf_swing (f, E, v)) \<subseteq> (banzhaf_swing (g, F, w))"
proof (unfold image_def, safe)
    fix
      A :: "'a set" and
      B :: "'a set" and
      V :: "'v set" and
      W :: "'v set" and
      p :: "('a, 'v) Profile" and
      q :: "('a, 'v) Profile"
    assume
      sw: "(A, V, p) \<in> banzhaf_swing (f, E, v)" and
      re2: "(B, W, q) = rename \<pi> (A, V, p)"
    (* swing votes are mapped to swing votes *)
    hence "\<exists> e'. ((A, V, p), e') \<in> swing_votes f E v"
      by simp
    then obtain e' :: "('a, 'v) Election" where 
      swing_pair: "((A, V, p), e') \<in> swing_votes f E v"
      by blast
    hence ineq: "fun\<^sub>\<E> f (A, V, p) \<noteq> fun\<^sub>\<E> f e'"
      unfolding swing_votes.simps
      by blast
    from swing_pair have eq_voters: "voters_\<E> (A, V, p) = voters_\<E> e'"
      unfolding swing_votes.simps
      by blast
    from swing_pair have coinc: "coincide_except (A, V, p) e' v"
      unfolding swing_votes.simps
      by blast
    (* voter sets after permuting are still equal *)
    from eq_voters have eq_voters': "voters_\<E> (rename \<pi> (A, V, p)) = voters_\<E> (rename \<pi> e')"
      by (metis rename.simps split_pairs2 voters_\<E>.simps)
    (* election outcomes after permuting are still inequal *)
    from ineq have ineq': 
      "fun\<^sub>\<E> (voting_power_measure.rename_rule \<pi> f) (rename \<pi> (A, V, p)) 
        \<noteq> fun\<^sub>\<E> (voting_power_measure.rename_rule \<pi> f) (rename \<pi> e')"
      using rename_roundtrip bij
      unfolding Bij_def
      by (metis Int_Collect)
    (* profiles after permuting still coincide everywhere except on w *)
    have "\<forall>x \<in> \<pi> ` V - {w}. the_inv \<pi> x \<in> V - {v}"
      using re bij
      unfolding voting_power_measure.rename_pow.simps
      by (metis (no_types, lifting) Bij_def Diff_iff Int_Collect 
            bij_betw_def empty_iff imageE insert_iff prod.inject the_inv_f_f)
    hence inv_set: "\<forall>x \<in> voters_\<E> (A, \<pi> ` V, p \<circ> the_inv \<pi>) - {w}. the_inv \<pi> x \<in> V - {v}"
      by (metis split_pairs2 voters_\<E>.simps)
    have
      "\<forall>e. \<forall>\<sigma>. \<sigma> \<in> Bij UNIV \<longrightarrow> (profile_\<E> (rename \<sigma> e) = (profile_\<E> e) \<circ> (the_inv \<sigma>))"
      by simp
    hence 
      "\<forall>e. \<forall>\<sigma>. \<sigma> \<in> Bij UNIV \<longrightarrow> (\<forall>v \<in> voters_\<E> e. profile_\<E> e v = profile_\<E> (rename \<sigma> e) (\<sigma> v))"
      by (simp add: Bij_def bij_betw_def the_inv_f_f)
    hence 
      "\<forall>e. \<forall>\<sigma>. \<sigma> \<in> Bij UNIV \<longrightarrow> (\<forall>v \<in> voters_\<E> (rename \<sigma> e). 
        profile_\<E> (rename \<sigma> e) v = profile_\<E> e (the_inv \<sigma> v))"
      by (simp add: Bij_def bij_betw_def the_inv_f_f)
    hence
      "\<forall>x \<in> voters_\<E> (A, \<pi> ` V, p \<circ> the_inv \<pi>) - {w}. 
        profile_\<E> (rename \<pi> e') x = profile_\<E> e' (the_inv \<pi> x)"
      using bij
      by (metis Diff_iff eq_voters' rename.simps)
    moreover have
      "\<forall>x \<in> voters_\<E> (A, \<pi> ` V, p \<circ> the_inv \<pi>) - {w}. 
        profile_\<E> (A, \<pi> ` V, p \<circ> the_inv \<pi>) x = p (the_inv \<pi> x)"
      by simp
    ultimately have coinc': "coincide_except (rename \<pi> (A, V, p)) (rename \<pi> e') w"
      using coinc inv_set
      unfolding coincide_except.simps rename.simps
      by (metis profile_\<E>.simps split_pairs2 voters_\<E>.simps)
    have valid: "((A, V, p), e') \<in> E \<times> E"
      using swing_pair
      unfolding banzhaf_swing.simps swing_votes.simps counting_domain.simps
      by blast
    hence valid': "((rename \<pi> (A, V, p)), (rename \<pi> e')) \<in> (rename \<pi> ` E) \<times> (rename \<pi> ` E)"
      by blast
    from valid' coinc' ineq' eq_voters' have
      "((rename \<pi> (A, V, p)), (rename \<pi> e')) \<in> 
          swing_votes (voting_power_measure.rename_rule \<pi> f) (rename \<pi> ` E) (\<pi> v)"
      using re
      unfolding swing_votes.simps voting_power_measure.rename_pow.simps
      by blast
    thus "(B, W, q) \<in> banzhaf_swing (g, F, w)"
      using re re2
      unfolding banzhaf_swing.simps voting_power_measure.rename_pow.simps
      by (metis (no_types, lifting) counting_domain.simps fst_conv left.simps 
            mem_Collect_eq rule.simps snd_conv voter.simps)
  qed

(* Elections on a fixed candidate and voter set form 
    a probability space using the uniform distribution*)
interpretation fixed_elec_uniform_distr: prob_space "uniform_count_measure elec"
  using finite non_empty 
  by (intro prob_space_uniform_count_measure)

(* The concrete function banzhaf_count satisfies all abstract characteristics of a Banzhaf index. *)
interpretation fixed_banzhaf: banzhaf_index banzhaf_count elec_domain banzhaf_swing
proof (unfold_locales)
  show "voting_power_measure.pow_symmetry banzhaf_count elec_domain" 
  proof (unfold voting_power_measure.pow_symmetry_def, simp del: uncurry3.simps, safe)
    fix
      f :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('v \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> 'c" and
      E :: "('a, 'v) Election set" and
      v :: 'v and
      g :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('v \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> 'c" and
      F :: "('a, 'v) Election set" and
      w :: 'v and
      \<pi> :: "'v \<Rightarrow> 'v"
    assume
      valid: "(f, E, v) \<in> elec_domain" and
      valid': "(g, F, w) \<in> elec_domain" and
      bij: "\<pi> \<in> Bij UNIV" and
      re: "voting_power_measure.rename_pow \<pi> (f, E, v) = (g, F, w)"
    have "inj_on (rename \<pi>) E"
      using Bij_def bij extensional_UNIV inf_top_left injD inj_onI mem_Collect_eq rename_inj
      by (metis (mono_tags, lifting))
    moreover have "(rename \<pi>) ` E = F"
      using re voting_power_measure.rename_pow.simps
      by (metis prod.inject)
    ultimately have "bij_betw (rename \<pi>) E F"
      unfolding bij_betw_def
      by blast
    (* equal amounts of votes in both elections *)
    hence card_eq: "card E = card F"
      using bij_betw_same_card 
      by blast
    have bij_inv: "the_inv \<pi> \<in> Bij UNIV"
      using bij
      by (simp add: Bij_def bij_betw_the_inv_into)
    moreover have inverse: "(rename \<pi>) \<circ> (rename (the_inv \<pi>)) = id"
      using bij_inv bij
      by (metis (no_types, lifting) Bij_def eq_id_iff extensional_UNIV inf_top_left
            left_right_inverse_eq mem_Collect_eq rename_inj rename_inv_commute the_inv_f_o_f_id)
    ultimately have "voting_power_measure.rename_pow (the_inv \<pi>) (g, F, w) = (f, E, v)"
      using re bij
      unfolding voting_power_measure.rename_pow.simps voting_power_measure.rename_rule.simps
      sorry
    with bij_inv have subset: 
      "rename (the_inv \<pi>) ` banzhaf_swing (g, F, w) \<subseteq> banzhaf_swing (f, E, v)"
      using valid' valid rename_presv_swing[of g F w f E v "the_inv \<pi>"]
      by blast
    with inverse have
      "(rename \<pi>) ` (rename (the_inv \<pi>)) ` banzhaf_swing (g, F, w) = banzhaf_swing (g, F, w)"
      by (metis (no_types, lifting) bij_betw_id bij_betw_imp_surj_on image_comp)
    with subset have "(banzhaf_swing (g, F, w)) \<subseteq> (rename \<pi>) ` (banzhaf_swing (f, E, v))"
      by (metis image_mono)
    moreover have "(rename \<pi>) ` (banzhaf_swing (f, E, v)) \<subseteq> (banzhaf_swing (g, F, w))"
      using valid valid' bij re rename_presv_swing[of f E v g F w \<pi>]
      by blast
    ultimately have "(banzhaf_swing (g, F, w)) = (rename \<pi>) ` (banzhaf_swing (f, E, v))"
      by blast
    moreover have "inj_on (rename \<pi>) (banzhaf_swing (f, E, v))"
      using Bij_def bij extensional_UNIV inf_top_left injD inj_onI mem_Collect_eq rename_inj
      by (metis (mono_tags, lifting))
    (* equal amounts of swing votes in both elections *)
    ultimately have "bij_betw (rename \<pi>) (banzhaf_swing (f, E, v)) (banzhaf_swing (g, F, w))"
      unfolding bij_betw_def
      by blast
    hence swing_eq: "card (banzhaf_swing (f, E, v)) = card (banzhaf_swing (g, F, w))"
      using bij_betw_same_card 
      by blast
    have "uncurry3 banzhaf_count (f, E, v) = banzhaf_count f E v"
      using uncurry3.simps[of banzhaf_count]
      by (metis case_prod_conv)
    also have "banzhaf_count f E v = (1/((card E)::real)) * (card (banzhaf_swing (f, E, v)))"
      by simp
    also have "(1/((card E)::real)) * (card (banzhaf_swing (f, E, v)))
      = (1/((card F)::real)) * (card (banzhaf_swing (g, F, w)))"
      using card_eq swing_eq
      by simp
    also have "(1/((card F)::real)) * (card (banzhaf_swing (g, F, w))) = banzhaf_count g F w"
      by simp
    also have "banzhaf_count g F w = uncurry3 banzhaf_count (g, F, w)"
      by simp
    finally show 
      "uncurry3 banzhaf_count (f, E, v) = uncurry3 banzhaf_count (g, F, w)"
      by simp
  qed
next
  show "voting_power_measure.ipower banzhaf_count elec_domain uniform_elections banzhaf_swing"
 proof (unfold voting_power_measure.ipower_def, safe)
    fix
      f :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('v \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> 'c" and
      E :: "('a, 'v) Election set" and
      v :: 'v
    assume
      valid: "(f, E, v) \<in> elec_domain"
    thus "prob_space (uniform_elections (f, E, v))"
      unfolding uniform_elections_def
      by (simp add: elec_domain_def fixed_elec_uniform_distr.prob_space_axioms)
  next
    fix
      f :: "'v set \<Rightarrow> 'a set \<Rightarrow> ('v \<Rightarrow> ('a \<times> 'a) set) \<Rightarrow> 'c" and
      E :: "('a, 'v) Election set" and
      v :: 'v
    assume
      valid: "(f, E, v) \<in> elec_domain"
    hence "finite E"
      unfolding elec_domain_def
      using finVot finAlt elec_def local.finite 
      by simp
    moreover have "banzhaf_swing (f, E, v) \<subseteq> E"
      by simp
    ultimately have
      "e2ennreal (banzhaf_count f E v) = 
        emeasure (uniform_elections (f, E, v)) (banzhaf_swing (f, E, v))"
      unfolding uniform_elections_def banzhaf_count.simps
      using emeasure_uniform_count_measure[of E "banzhaf_swing (f, E, v)"]
      by (metis counting_domain.simps divide_inverse e2ennreal_ereal 
                fst_conv inverse_eq_divide mult.commute snd_conv)
    thus 
      "e2ennreal (banzhaf_count (rule (f, E, v)) (counting_domain (f, E, v)) (voter (f, E, v))) 
        = emeasure (uniform_elections (f, E, v)) (banzhaf_swing (f, E, v))"
      by (metis counting_domain.simps rule.simps split_pairs2 voter.simps)
  qed
qed
  
end

(*


fun weighted_voting_power :: 
  "('a, 'v, 'r) Electoral_Module \<Rightarrow> ('a, 'v) Election set \<Rightarrow>
  ('a, 'v, 'r) Swing_Weight \<Rightarrow> 'v \<Rightarrow> ereal" where
  "weighted_voting_power f E weight v = (\<Sum> e \<in> E. weight f e v)"


fun discrete_dist :: "'x Distance" where
  "discrete_dist x y = (if (x = y) then 0 else 1)"

text \<open>
  The raw weight of an election e is the total distance 
  that can be achieved summed over ALL its different swing votes\<close>
fun raw_weight :: 
  "'r Distance \<Rightarrow> ('a, 'v) Election set \<Rightarrow> ('a, 'v, 'r) Swing_Weight" where
  "raw_weight d E f e v = (\<Sum> (e1, e2) \<in> swing_votes f E v. 
    (1 - discrete_dist e1 e) * (d (fun\<^sub>\<E> f e1) (fun\<^sub>\<E> f e2)))"

text \<open>
  Raw power defines the weights of swing elections as the 
  total result distance achievable via swing voting.\<close>
fun raw_power :: "'r Distance \<Rightarrow> ('a, 'v, 'r) Voting_Power" where
  "raw_power d f E v = weighted_voting_power f E (raw_weight d E) v"

*)
*)