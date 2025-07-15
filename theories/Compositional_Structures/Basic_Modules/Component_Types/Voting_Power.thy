section \<open>Voting Power\<close>

theory Voting_Power
  imports Electoral_Module
          Distance    
          "HOL-Probability.Probability_Measure"

begin

subsection \<open>Auxiliary Lemmas\<close>

fun swap_voters :: "'v \<Rightarrow> 'v \<Rightarrow> ('a, 'v) Election \<Rightarrow> ('a, 'v) Election" where
  "swap_voters v w e = 
    (let \<pi> = (\<lambda>x::'v. (if x = w then v else (if x = v then w else x))) in
      rename \<pi> e)"

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

subsection \<open>Definitions\<close>

type_synonym ('a, 'v, 'r) Swing_Weight =
  "('a, 'v, 'r) Electoral_Module \<Rightarrow> ('a, 'v) Election \<Rightarrow> 'v \<Rightarrow> ereal"

type_synonym ('a, 'v, 'r) Voting_Power =
  "('a, 'v, 'r) Electoral_Module \<Rightarrow> ('a, 'v) Election set \<Rightarrow> 'v \<Rightarrow> ereal"

type_synonym ('a, 'v, 'r) Voting_Power_Domain =
  "('a, 'v, 'r) Electoral_Module \<times> ('a, 'v) Election set \<times> 'v"

fun rule :: "('a, 'v, 'r) Voting_Power_Domain \<Rightarrow> ('a, 'v, 'r) Electoral_Module" where
  "rule X = fst X"

fun counting_domain :: "('a, 'v, 'r) Voting_Power_Domain \<Rightarrow> ('a, 'v) Election set" where
  "counting_domain X = fst (snd X)"

fun voter :: "('a, 'v, 'r) Voting_Power_Domain \<Rightarrow> 'v" where
  "voter X = snd (snd X)"

subsection \<open>Abstract Voting Power Indices and their Characterisations\<close>

locale voting_power_measure =
  fixes 
    \<delta> :: "('a, 'v, 'r) Voting_Power" and
    domain :: "('a, 'v, 'r) Voting_Power_Domain set" 
    (* domain on which delta operates *)
    (* every element defines a concrete configuration in which to determine a voters power:
        the voting rule, the voter as well as the domain of valid profiles/elections to consider *)
begin

text \<open>Symmetry of Voting Power Measures\<close>

fun rename_rule :: 
  "('v \<Rightarrow> 'v) \<Rightarrow> ('a, 'v, 'r) Electoral_Module \<Rightarrow> ('a, 'v, 'r) Electoral_Module" where
  "rename_rule \<pi> f = (\<lambda> V A p. (fun\<^sub>\<E> f) ((the_inv (rename \<pi>)) (A, V, p)))"

fun rename_pow :: 
  "('v \<Rightarrow> 'v) \<Rightarrow> (('a, 'v, 'r) Voting_Power_Domain \<Rightarrow> ('a, 'v, 'r) Voting_Power_Domain)" where
  "rename_pow \<pi> (f, E, v) = (rename_rule \<pi> f, (rename \<pi>) ` E, \<pi> v)"

fun uncurry3 :: "('w \<Rightarrow> 'x \<Rightarrow> 'y \<Rightarrow> 'z) \<Rightarrow> (('w \<times> 'x \<times> 'y) \<Rightarrow> 'z)" where
  "uncurry3 f = (\<lambda>(w,x,y). f w x y)"

definition pow_symmetry :: bool where 
  "pow_symmetry = (is_symmetry (uncurry3 \<delta>) (Invariance 
    (action_induced_rel (Bij (UNIV::('v set))) domain (\<lambda> \<pi>. rename_pow \<pi>))))"

text \<open>I-Power Interpretation of Voting Power Measures\<close>

definition ipower :: 
  "(('a, 'v, 'r) Voting_Power_Domain \<Rightarrow> ('a, 'v) Election measure) \<Rightarrow>
    (('a, 'v, 'r) Voting_Power_Domain \<Rightarrow> ('a, 'v) Election set) \<Rightarrow> 
      bool" 
  where 
    "ipower M event = (\<forall> X \<in> domain. prob_space (M X) \<and>
      \<delta> (rule X) (counting_domain X) (voter X) = (emeasure (M X)) (event X))"

lemma anon_rule_imp_symmetry_pow_const:
  fixes
    f :: "('a, 'v, 'r) Electoral_Module" and
    E :: "('a, 'v) Election set" and
    X :: "('a, 'v, 'r) Voting_Power_Domain set" and
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
    valid_v: "(f, E, v) \<in> X"
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
      action_induced_rel (Bij (UNIV::('v set))) X (\<lambda> \<pi>. rename_pow \<pi>)"
    using valid_v
    by simp
  hence eq0: "\<delta> f E v = \<delta> (rename_rule ?\<pi> f) ((rename ?\<pi>) ` E) (?\<pi> v)"
    using sym_pow
    unfolding pow_symmetry_def
    sorry
  (* pi(v) = w, E_pi = E and f_pi = f (constrained to E) yields the result 
    given that delta does not care about values of f outside of E. *)
  have 
    "\<forall> e \<in> E. extensional_continuation (the_inv (rename ?\<pi>)) E e = 
                (the_inv (rename ?\<pi>)) e"
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

end

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

subsection \<open>Concrete Voting Power Indices\<close>

fun coincide_except :: "('a, 'v) Election \<Rightarrow> ('a, 'v) Election \<Rightarrow> 'v \<Rightarrow> bool" where
  "coincide_except e1 e2 v = 
      (\<forall> w \<in> (voters_\<E> e1) - {v}. profile_\<E> e1 w = profile_\<E> e2 w)"

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

(* Elections on a fixed candidate and voter set form 
    a probability space using the uniform distribution*)
interpretation fixed_elec_uniform_dist: prob_space "uniform_count_measure elec"
  using finite non_empty 
  by (intro prob_space_uniform_count_measure)

interpretation fixed_banzhaf: banzhaf_index banzhaf_count elec_domain banzhaf_swing
proof (unfold_locales)
  show "voting_power_measure.pow_symmetry banzhaf_count elec_domain" 
    sorry
next
  show "voting_power_measure.ipower banzhaf_count elec_domain uniform_elections banzhaf_swing"
    sorry
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

end