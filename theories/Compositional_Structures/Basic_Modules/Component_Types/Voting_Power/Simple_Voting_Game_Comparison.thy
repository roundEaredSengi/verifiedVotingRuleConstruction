theory Simple_Voting_Game_Comparison
  imports Simple_Voting_Game
          Voting_Power_Comparison

begin

section \<open>Simple Voting Game Model Comparison\<close>

text \<open>
A voting rule \<^latex>\<open>\<R>\<close> is equivalent to an SVG \<^latex>\<open>\<G>\<close> if it "behaves like the SVG".
For this to be the case, the voting rule must have exactly two possible ballots, two possible 
results and there must be a bijection between ballots and results that yields a notion of 
"voting for a specific result" (by voting for its corresponding ballot).
Given this bijection, there must be a distinguished result that corresponds to the "yes" option
in the SVG latex>\<open>\<G>\<close>.
\<close>
definition svg_rule_equivalence :: 
  "'b \<Rightarrow> 'b \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> ('v, 'b, 'r) Voting_Rule \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> bool" where
  "svg_rule_equivalence b1 b2 r1 r2 \<R> \<G> = (\<R> = svg_rule b1 b2 r1 r2 \<G>)"

locale rule_simple_voting_game_comparison = 
  m1: voting_rule_model RuleSet + 
  m2: simple_voting_game_model GameSet ballot1 ballot2 result1 result2
  for RuleSet :: "('v, 'b, 'r) Voting_Rule set" and GameSet :: "'v Simple_Voting_Game set" and 
    ballot1 :: 'b and ballot2 and result1 :: 'r and result2
begin

interpretation svg: simple_voting_game_model GameSet ballot1 ballot2 result1 result2
  by unfold_locales

interpretation rule: voting_rule_model RuleSet
  by unfold_locales

end

(* Show that the given equivalence function for SVGs and voting rules is a valid comparison map *)
sublocale
  rule_simple_voting_game_comparison \<subseteq> 
    voting_model_comparison 
      RuleSet GameSet id "svg_rule ballot1 ballot2 result1 result2" 
      "svg_rule_equivalence ballot1 ballot2 result1 result2"
by (unfold_locales, unfold svg_rule_equivalence_def, simp_all)

(* Variante 2:

locale rule_simple_voting_game_comparison_2 = 
  voting_model_comparison 
      rule_voters rule_results rule_ballots rule_tallying 
      voters_svg "\<lambda>G. {a, b}" "\<lambda>G. {x, y}" "tallying_method x y a b"
      "svg_rule_equivalence \<circ> Rep_Valid_Voting_Rule"
      for x :: 'b and y and a :: 'r and b
begin 

interpretation svg: simple_voting_game_model x y a b
  sorry (* TODO does not work without additional assms *)

interpretation svg: voting_model 
  "TYPE(('v, 'b, 'r) Valid_Voting_Rule)" rule_voters rule_results rule_ballots rule_tallying
  by unfold_locales

end

sublocale
  rule_simple_voting_game_comparison_2 \<subseteq> 
    voting_model_comparison ...

*)

section \<open>Simple Voting Game Power Comparison\<close>

locale svg_power_comparison = 
  pow1: svg_power S b1 b2 r1 r2 \<delta>1 +
  pow2: voting_power domain2 semantics2 \<delta>2 +
  comp: 
    voting_model_comparison S domain2 "svg_rule b1 b2 r1 r2" semantics2 model_equivalence
      for model_equivalence :: "'v Simple_Voting_Game \<Rightarrow> '\<beta> \<Rightarrow> bool" and
          S :: "'v Simple_Voting_Game set" and b1 :: 'b and b2 :: 'b and r1 :: 'r and r2 :: 'r and 
          \<delta>1 and domain2 and semantics2 :: "('\<beta>, 'v, 'b, 'r) Voting_Rule_Transformation" and \<delta>2

sublocale svg_power_comparison \<subseteq>
  voting_power_comparison
    model_equivalence S "svg_rule b1 b2 r1 r2" \<delta>1 domain2 semantics2 \<delta>2
  by unfold_locales

(*
theorem (in svg_power_comparison) null_player_extension:
  "axiom_equivalence
    (null_player_axiom_axioms S (svg_rule b1 b2 r1 r2)) 
    (null_player_axiom_axioms domain2 semantics2)"
proof (unfold axiom_equivalence.simps null_player_axiom_axioms_def, safe)
  fix x :: "'\<beta>" and v :: 'v
  assume 
    equiv: "comp.domain_equivalence" and equal: "power_equality" and
    "x \<in> domain2" and "v \<in> pow2.voters x" and no_swing: "pow2.has_swing x v = (\<lambda>p. False)" and
    np_games: 
      "\<forall>\<G> \<in> S. \<forall>v \<in> pow1.svg.mod.voters \<G>. pow1.svg.mod.has_swing \<G> v = (\<lambda>p. False) \<longrightarrow> \<delta>1 \<G> v = 0"
  then obtain \<G> :: "'v Simple_Voting_Game" where "\<G> \<in> S" and eq: "model_equivalence \<G> x"
    using equiv
    unfolding comp.domain_equivalence_def
    by metis
  hence "v \<in> pow1.svg.mod.voters \<G>"
    using \<open>x \<in> domain2\<close> \<open>v \<in> pow2.voters x\<close> comp.equiv_sane
    by metis
  moreover have "pow1.svg.mod.has_swing \<G> v = (\<lambda>p. False)"
  proof (rule ccontr)
    assume "pow1.svg.mod.has_swing \<G> v \<noteq> (\<lambda>p. False)"
    hence "\<exists>p :: ('v, 'b) Profile. pow1.svg.mod.has_swing \<G> v p"
      by metis
    then obtain p :: "('v, 'b) Profile" and q :: "('v, 'b) Profile" where
      "pow1.svg.mod.differ_only_on v p q" and 
      "pow1.svg.mod.valid_voter \<G> v" and 
      "rule (svg_rule b1 b2 r1 r2 \<G>) p \<noteq> rule (svg_rule b1 b2 r1 r2 \<G>) q"
      unfolding pow1.svg.mod.has_swing.simps
      by auto
    hence "rule (semantics2 x) p \<noteq> rule (semantics2 x) q"
      using eq comp.equiv_sane \<open>x \<in> domain2\<close> \<open>\<G> \<in> S\<close>
      by simp
    thus "False"
      using no_swing \<open>v \<in> pow2.voters x\<close> \<open>pow2.differ_only_on v p q\<close>
      unfolding pow2.has_swing.simps pow2.is_single_swing.simps
      by meson
  qed
  ultimately have "\<delta>1 \<G> v = 0"
    using \<open>\<G> \<in> S\<close> np_games
    by metis
  moreover have "\<delta>2 x v = \<delta>1 \<G> v"
    using \<open>\<G> \<in> S\<close> eq equal \<open>v \<in> pow2.voters x\<close> \<open>x \<in> domain2\<close> comp.equiv_sane
    unfolding power_equality_def
    by metis
  ultimately show "\<delta>2 x v = 0"
    by simp
next
  fix V :: "'v set" and \<F> :: "'v set set" and v :: 'v
  assume
    equiv: "comp.domain_equivalence" and equal: "power_equality" and
    "(V, \<F>) \<in> S" and "v \<in> pow1.svg.mod.voters (V, \<F>)" and 
    no_swing: "pow1.svg.mod.has_swing (V, \<F>) v = (\<lambda>p. False)" and
    np_other: "\<forall>x \<in> domain2. \<forall>v \<in> pow2.voters x. pow2.has_swing x v = (\<lambda>p. False) \<longrightarrow> \<delta>2 x v = 0"
  then obtain x :: '\<beta> where "x \<in> domain2" and eq: "model_equivalence (V, \<F>) x"
    using equiv
    unfolding comp.domain_equivalence_def
    by metis
  hence "v \<in> pow2.voters x"
    using \<open>(V, \<F>) \<in> S\<close> \<open>v \<in> pow1.svg.mod.voters (V, \<F>)\<close> comp.equiv_sane
    by metis
  moreover have "pow2.has_swing x v = (\<lambda>p. False)"
  proof (rule ccontr)
    assume "pow2.has_swing x v \<noteq> (\<lambda>p. False)"
    hence "\<exists>p. pow2.has_swing x v p"
      by metis
    then obtain p :: "('v, 'b) Profile" and q :: "('v, 'b) Profile" where
      "pow2.differ_only_on v p q" and 
      "pow2.valid_voter x v" and 
      "rule (semantics2 x) p \<noteq> rule (semantics2 x) q"
      unfolding pow2.has_swing.simps
      by auto
    hence "rule (svg_rule b1 b2 r1 r2 (V, \<F>)) p \<noteq> rule (svg_rule b1 b2 r1 r2 (V, \<F>)) q"
      using eq comp.equiv_sane \<open>x \<in> domain2\<close> \<open>(V, \<F>) \<in> S\<close>
      by presburger
    thus "False"
      using no_swing \<open>v \<in> pow1.svg.mod.voters (V, \<F>)\<close> \<open>pow1.svg.mod.differ_only_on v p q\<close>
      unfolding pow1.svg.mod.has_swing.simps pow1.svg.mod.is_single_swing.simps
      by meson
  qed
  ultimately have "\<delta>2 x v = 0"
    using \<open>x \<in> domain2\<close> np_other
    by metis
  moreover have "\<delta>1 (V, \<F>) v = \<delta>2 x v"
    using \<open>(V, \<F>) \<in> S\<close> eq equal \<open>v \<in> pow1.svg.mod.voters (V, \<F>)\<close> \<open>x \<in> domain2\<close> comp.equiv_sane
    unfolding power_equality_def
    by metis
  ultimately show "\<delta>1 (V, \<F>) v = 0"
    by simp
qed

lemma (in svg_power_comparison) svg_isomorphism_sanity:
  "pow1.isomorphism_sanity svg_isomorphism"
proof (simp, safe)
  fix V :: "'v set" and \<F> :: "'v set set" and 
    V' :: "'v set" and \<F>' :: "'v set set" and 
    \<sigma> :: "'v \<Rightarrow> 'v" and b :: 'b
  assume "(V, \<F>) \<in> S" and "(V', \<F>') \<in> S" and "(V', \<F>') = svg_isomorphism \<sigma> (V, \<F>)" and
    "bij_betw \<sigma> (pow1.svg.mod.voters (V, \<F>)) (pow1.svg.mod.voters (V', \<F>'))" and
    "b \<in> pow1.svg.mod.ballots (V, \<F>)"
  thus "b \<in> pow1.svg.mod.ballots (svg_isomorphism \<sigma> (V, \<F>))"
    by simp
next
  fix V :: "'v set" and \<F> :: "'v set set" and 
    V' :: "'v set" and \<F>' :: "'v set set" and 
    \<sigma> :: "'v \<Rightarrow> 'v" and b :: 'b
  assume "(V, \<F>) \<in> S" and "(V', \<F>') \<in> S" and "(V', \<F>') = svg_isomorphism \<sigma> (V, \<F>)" and
    "bij_betw \<sigma> (pow1.svg.mod.voters (V, \<F>)) (pow1.svg.mod.voters (V', \<F>'))" and
    "b \<in> pow1.svg.mod.ballots (svg_isomorphism \<sigma> (V, \<F>))"
  thus "b \<in> pow1.svg.mod.ballots (V, \<F>)"
    by simp
next
  fix V :: "'v set" and \<F> :: "'v set set" and 
    V' :: "'v set" and \<F>' :: "'v set set" and 
    \<sigma> :: "'v \<Rightarrow> 'v" and r :: 'r
  assume "(V, \<F>) \<in> S" and "(V', \<F>') \<in> S" and "(V', \<F>') = svg_isomorphism \<sigma> (V, \<F>)" and
    "bij_betw \<sigma> (pow1.svg.mod.voters (V, \<F>)) (pow1.svg.mod.voters (V', \<F>'))" and
    "r \<in> pow1.svg.mod.results (V, \<F>)"
  thus "r \<in> pow1.svg.mod.results (svg_isomorphism \<sigma> (V, \<F>))"
    by simp
next
  fix V :: "'v set" and \<F> :: "'v set set" and 
    V' :: "'v set" and \<F>' :: "'v set set" and 
    \<sigma> :: "'v \<Rightarrow> 'v" and r :: 'r
  assume "(V, \<F>) \<in> S" and "(V', \<F>') \<in> S" and "(V', \<F>') = svg_isomorphism \<sigma> (V, \<F>)" and
    "bij_betw \<sigma> (pow1.svg.mod.voters (V, \<F>)) (pow1.svg.mod.voters (V', \<F>'))" and
    "r \<in> pow1.svg.mod.results (svg_isomorphism \<sigma> (V, \<F>))"
  thus "r \<in> pow1.svg.mod.results (V, \<F>)"
    by simp
next
  fix V :: "'v set" and \<F> :: "'v set set" and 
    V' :: "'v set" and \<F>' :: "'v set set" and 
    \<sigma> :: "'v \<Rightarrow> 'v" and p :: "('v, 'b) Profile"
  assume "(V, \<F>) \<in> S" and "(V', \<F>') \<in> S" and iso: "(V', \<F>') = svg_isomorphism \<sigma> (V, \<F>)" and
    bij: "bij_betw \<sigma> (pow1.svg.mod.voters (V, \<F>)) (pow1.svg.mod.voters (V', \<F>'))" and
    prof: "p \<in> pow1.svg.mod.voters (svg_isomorphism \<sigma> (V, \<F>)) \<rightarrow> 
                pow1.svg.mod.ballots (svg_isomorphism \<sigma> (V, \<F>))"
  have 
    "pow1.svg.mod.aggregation (V, \<F>) (p \<circ> \<sigma>) = (if (preimg_in V (p \<circ> \<sigma>) {b1} \<in> \<F>) then r1 else r2)"
    by simp
  also have "... = (if (preimg_in (the_inv \<sigma> ` V) p {b1} \<in> (image \<sigma>) ` \<F>) then r1 else r2)"
    sorry
  also have "... = pow1.svg.mod.aggregation (svg_isomorphism \<sigma> (V, \<F>)) p"
    using iso bij
    sorry
  finally show "pow1.svg.mod.aggregation (V, \<F>) (p \<circ> \<sigma>) = 
    pow1.svg.mod.aggregation (svg_isomorphism \<sigma> (V, \<F>)) p"
    by satx
qed

theorem (in svg_power_comparison) symmetry_extension:
  fixes
    isomorphism2 :: "('v \<Rightarrow> 'v) \<Rightarrow> '\<beta> \<Rightarrow> '\<beta>"
  assumes
    iso_sane: "pow2.isomorphism_sanity isomorphism2"
    (* compare this assumption to assuming the following:
      "\<forall>x \<in> domain2. \<forall>\<G> \<in> S. model_equivalence \<G> x \<longrightarrow> 
        (\<forall>\<sigma>. bij_betw \<sigma> (voters x) (voters x) \<longrightarrow> 
          model_equivalence (svg_isomorphism \<sigma> \<G>) (isomorphism \<sigma> x))" *)
  shows 
    "axiom_equivalence 
      (\<lambda>\<delta>. symmetry_axiom_axioms S (svg_rule b1 b2 r1 r2) \<delta> svg_isomorphism) 
      (\<lambda>\<delta>. symmetry_axiom_axioms domain2 semantics2 \<delta> isomorphism2)"
proof (unfold axiom_equivalence.simps symmetry_axiom_axioms_def, safe)
  show "pow2.isomorphism_sanity isomorphism2"
    using assms
    by satx
next
  assume 
    equiv: "comp.domain_equivalence" and
    equal: "power_equality" and
    sane1: "pow1.isomorphism_sanity svg_isomorphism" and 
    sym1: "pow1.symmetry svg_isomorphism"
  show "pow2.symmetry isomorphism2"
  proof (simp only: pow2.symmetry.simps, safe)
    fix m :: '\<beta> and v :: 'v and \<sigma> :: "'v \<Rightarrow> 'v" and p :: "('v, 'b) Profile"
    assume
      dom: "m \<in> domain2" and dom': "isomorphism2 \<sigma> m \<in> domain2" and vot: "v \<in> pow2.voters m" and
      bij: "bij_betw \<sigma> (pow2.voters m) (pow2.voters (isomorphism2 \<sigma> m))" 
    hence vot': "\<sigma> v \<in> pow2.voters (isomorphism2 \<sigma> m)"
      by (meson bij_betwE)
    from dom dom' vot obtain G :: "'v Simple_Voting_Game" and G' :: "'v Simple_Voting_Game" where 
      "G \<in> S" and "G' \<in> S" and 
      equiv1: "model_equivalence G m" and equiv2: "model_equivalence G' (isomorphism2 \<sigma> m)"
      using equiv
      unfolding comp.domain_equivalence_def
      by metis
    hence game_bij: "bij_betw \<sigma> (pow1.svg.mod.voters G) (pow1.svg.mod.voters G')"
      using comp.equiv_sane bij dom dom'
      by presburger
    have "rule_voters (svg_rule b1 b2 r1 r2 G') = \<sigma> ` (rule_voters (svg_rule b1 b2 r1 r2 G))" 
      using equiv1 equiv2 \<open>G \<in> S\<close> \<open>G' \<in> S\<close> comp.equiv_sane bij bij_betw_imp_surj_on dom dom'
      by metis
    hence game_vot_eq: "fst G' = \<sigma> ` fst G"
      using svg_rule.simps
      by (metis fst_conv prod.collapse)
    have "\<forall>p \<in> pow2.profiles (isomorphism2 \<sigma> m). 
      rule (semantics2 m) (p \<circ> \<sigma>) = rule (semantics2 (isomorphism2 \<sigma> m)) p"
      using iso_sane bij dom dom'
      by simp
    hence "\<forall>p \<in> pow1.svg.mod.profiles G'. 
      rule (svg_rule b1 b2 r1 r2 G) (p \<circ> \<sigma>) = rule (svg_rule b1 b2 r1 r2 G') p"
      using equiv1 equiv2 comp.equiv_sane bij dom dom' \<open>G \<in> S\<close> \<open>G' \<in> S\<close>
      by simp
    hence game_rule_eq: "\<forall>p \<in> pow1.svg.mod.profiles G'. 
      aggregation_method b1 b2 r1 r2 G (p \<circ> \<sigma>) = aggregation_method b1 b2 r1 r2 G' p"
      using svg_rule.simps prod.collapse snd_conv
      by metis
    have "snd G' = (image \<sigma>) ` snd G"
    proof (safe)
      fix X :: "'v set"
      assume "X \<in> coalitions G'"
      hence valid: "X \<subseteq> pow1.svg.mod.voters G'"
        using \<open>G' \<in> S\<close> pow1.svg.simple_voting_game_model_axioms
        unfolding simple_voting_game_model_def simple_voting_game_model_axioms_def
        by auto
      then obtain Y :: "'v set" where inv: "Y = the_inv_into (pow1.svg.mod.voters G) \<sigma> ` X"
        using game_bij
        by metis
      define p :: "('v, 'b) Profile" where "p = (\<lambda>x. (if x \<in> X then b1 else b2))"
      have "rule_profile (svg_rule b1 b2 r1 r2 G') p"
        using Pi_def[of "pow1.svg.mod.voters G'" "\<lambda>x. {b1, b2}"] 
              svg_rule.simps[of b1 b2 r1 r2 "fst G'" "snd G'"]
        unfolding p_def
        by simp
      hence "p \<in> pow1.svg.mod.profiles G'"
        by simp
      hence aggr_eq: 
        "aggregation_method b1 b2 r1 r2 G' p = aggregation_method b1 b2 r1 r2 G (p \<circ> \<sigma>)"
        using game_rule_eq
        by presburger
      have "X \<subseteq> preimg_in (pow1.svg.mod.voters G') p {b1}"
        unfolding p_def preimg_in.simps
        using valid
        by auto
      moreover have "X \<supseteq> preimg_in (pow1.svg.mod.voters G') p {b1}"
        using pow1.svg.simple_voting_game_model_axioms
        unfolding p_def preimg_in.simps simple_voting_game_model_def 
                  simple_voting_game_model_axioms_def
        by auto
      ultimately have preX: "X = preimg_in (pow1.svg.mod.voters G') p {b1}"
        by simp
      hence "aggregation_method b1 b2 r1 r2 G' p = r1"
        using \<open>X \<in> coalitions G'\<close>
        by (metis aggregation_method.simps fst_conv prod.collapse svg_rule.simps)
      hence "aggregation_method b1 b2 r1 r2 G (p \<circ> \<sigma>) = r1"
        using aggr_eq
        by simp
      hence "preimg_in (fst G) (p \<circ> \<sigma>) {b1} \<in> coalitions G"
        using pow1.svg.simple_voting_game_model_axioms prod.collapse[of G] aggregation_method.simps
        unfolding simple_voting_game_model_def simple_voting_game_model_axioms_def
        by metis
      moreover have "Y = preimg_in (pow1.svg.mod.voters G) (p \<circ> \<sigma>) {b1}"
        using inv preX (* TODO: show Y = sigma^{-1}(p^{-1}({b1}) *)
        sorry
      moreover have "X = \<sigma> ` Y"
        using inv game_bij valid f_the_inv_into_f[of \<sigma> "pow1.svg.mod.voters G"]
        sorry
      moreover have "pow1.svg.mod.voters G = fst G"
        by (metis fst_conv surjective_pairing svg_rule.simps)
      ultimately show "X \<in> (image \<sigma>) ` coalitions G"
        by simp
    next
      fix X :: "'v set"
      assume "X \<in> coalitions G"
      thus "\<sigma> ` X \<in> coalitions G'"
        sorry
    qed
    hence iso: "G' = svg_isomorphism \<sigma> G"
      using game_vot_eq svg_isomorphism.simps prod.collapse
      by metis
    have "\<delta>2 m v = \<delta>1 G v"
      using equiv1 equal \<open>m \<in> domain2\<close> vot \<open>G \<in> S\<close> dom comp.equiv_sane power_equality_def 
      by presburger
    moreover have "\<delta>2 (isomorphism2 \<sigma> m) (\<sigma> v) = \<delta>1 G' (\<sigma> v)"
      using equiv2 equal \<open>m \<in> domain2\<close> vot' \<open>G' \<in> S\<close> dom' comp.equiv_sane power_equality_def
      by presburger
    moreover have "\<delta>1 G v = \<delta>1 G' (\<sigma> v)"
      using iso bij sym1 \<open>G \<in> S\<close> \<open>G' \<in> S\<close> comp.equiv_sane dom dom' vot equiv1 equiv2
      unfolding pow1.symmetry.simps
      by presburger
    ultimately show "\<delta>2 m v = \<delta>2 (isomorphism2 \<sigma> m) (\<sigma> v)"
      by simp
  qed
next
  show "pow1.isomorphism_sanity svg_isomorphism"
    by (rule svg_isomorphism_sanity)
next
  assume
    "pow2.isomorphism_sanity isomorphism2" and
    "pow2.symmetry isomorphism2"
  thus "pow1.symmetry svg_isomorphism"
    sorry
qed
*)

end