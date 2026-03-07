theory Voting_Power_Comparison
  imports Voting_Power_Scratch
          Simple_Voting_Game
          Voting_Rule

begin

(*
locale Voting_Model_Comparison =
  fixes
    model_similarity :: "'x \<Rightarrow> 'y \<Rightarrow> bool"

locale Voting_Power_Comparison =
  fixes 
    delta1 :: "('x, 'v) Voting_Power" and
    delta2 :: "('y, 'v) Voting_Power" and
    similarity :: "('x, 'v) Voting_Power \<Rightarrow> ('y, 'v) Voting_Power \<Rightarrow> bool"
  assumes
    "similarity delta1 delta2"

definition (in Voting_Model_Comparison) numerical_similarity :: 
  "('x, 'v) Voting_Power \<Rightarrow> ('y, 'v) Voting_Power \<Rightarrow> bool" where
  "numerical_similarity delta1 delta2 = (\<forall>m1 m2. model_similarity m1 m2 \<longrightarrow> (\<forall>v. delta1 m1 v = delta2 m2 v))"

locale Numerical_Voting_Power_Comparison = 
    model_comp: Voting_Model_Comparison model_similarity + 
    power_comp: Voting_Power_Comparison delta1 delta2 model_comp.numerical_similarity 
    for model1 and model2 and model_similarity and delta1 and delta2
begin

thm power_comp.Voting_Power_Comparison_axioms

end 
*)

fun preimg_in :: "'x set \<Rightarrow> ('x \<Rightarrow> 'y) \<Rightarrow> 'y set \<Rightarrow> 'x set" where
  "preimg_in X f Y = {x |x. x \<in> X \<and> f x \<in> Y}"

definition svg_rule_equivalence :: 
  "('v, 'b, 'r) Voting_Rule \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> bool" where
  "svg_rule_equivalence \<R> \<G> = (
    voters \<R> = fst \<G> \<and>
    card (ballots \<R>) = 2 \<and> 
    card (results \<R>) = 2 \<and> 
    (\<exists>\<sigma>::'b \<Rightarrow> 'r. \<exists>r \<in> results \<R>. bij_betw \<sigma> (ballots \<R>) (results \<R>) \<and>
      (\<forall>p. rule \<R> p = r \<longleftrightarrow> preimg_in (voters \<R>) p (preimg_in (ballots \<R>) \<sigma> {r}) \<in> (coalitions \<G>))
    )
  )"

definition svg_rule_power_equivalence ::
  "(('v, 'b, 'r) Voting_Rule, 'v) Voting_Power \<Rightarrow> ('v Simple_Voting_Game, 'v) Voting_Power \<Rightarrow> bool"
  where 
    "svg_rule_power_equivalence \<delta>1 \<delta>2 = (
      \<forall>\<R> \<G>. svg_rule_equivalence \<R> \<G> \<longrightarrow> (\<forall>v \<in> voters \<R> \<inter> fst \<G>. \<delta>1 \<R> v = \<delta>2 \<G> v)
    )"

definition svg_rule_axiom_equivalence ::
  "(('v, 'b, 'r) Voting_Rule, 'v) Voting_Power_Axiom \<Rightarrow> 
    ('v Simple_Voting_Game, 'v) Voting_Power_Axiom \<Rightarrow> bool" where
  "svg_rule_axiom_equivalence \<phi>1 \<phi>2 = (\<forall>m1 m2 \<delta>1 \<delta>2. 
    svg_rule_equivalence m1 m2 \<and> svg_rule_power_equivalence \<delta>1 \<delta>2 \<longrightarrow> (\<phi>1 {m1} \<delta>1 \<longleftrightarrow> \<phi>2 {m2} \<delta>2))"

theorem block_equivalence:
  "svg_rule_axiom_equivalence block_axiom_rule block_axiom_svg_on"
  sorry

theorem banzhaf_equivalence:
  "svg_rule_power_equivalence banzhaf_rule_1 banzhaf_svg_1"
  sorry

theorem block_satisfied_by_rule_banzhaf:
  "block_axiom_rule {} banzhaf_rule_1" (* TODO: define monotone binary voting rules *)
  sorry

end