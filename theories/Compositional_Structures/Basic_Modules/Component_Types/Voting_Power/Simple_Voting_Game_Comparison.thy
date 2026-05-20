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
  "svg_rule_equivalence ball1 ball2 res1 res2 \<R> \<G> = (
    voters \<R> = fst \<G> \<and>
    ballots \<R> = {ball1, ball2} \<and> ball1 \<noteq> ball2 \<and>
    results \<R> = {res1, res2} \<and> res1 \<noteq> res2 \<and>
    (\<exists>\<sigma>::'b \<Rightarrow> 'r. \<exists>r \<in> results \<R>. bij_betw \<sigma> (ballots \<R>) (results \<R>) \<and>
      (\<forall>p. rule \<R> p = r \<longleftrightarrow> preimg_in (voters \<R>) p (preimg_in (ballots \<R>) \<sigma> {r}) \<in> (coalitions \<G>))
    )
  )" (* reformulate last property using res1, res2? *)

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
      RuleSet GameSet 
      voters voters_svg 
      ballots "\<lambda>G. {ballot1, ballot2}" 
      results "\<lambda>G. {result1, result2}"  
      rule "aggregation_method ballot1 ballot2 result1 result2"
            "svg_rule_equivalence ballot1 ballot2 result1 result2"
  apply unfold_locales
  apply (unfold svg_rule_equivalence_def)
  apply simp
  apply clarify
  sorry

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
  pow2: voting_power domain2 voters2 ballots2 results2 aggregation2 \<delta>2 +
  comp: 
    voting_model_comparison 
      S domain2 voters_svg voters2 "\<lambda>G. {b1, b2}" ballots2 
      "\<lambda>G. {r1, r2}" results2 "aggregation_method b1 b2 r1 r2" aggregation2
      model_equivalence
      for model_equivalence :: "'v Simple_Voting_Game \<Rightarrow> '\<beta> \<Rightarrow> bool" and
          S and b1 :: 'b and b2 :: 'b and r1 :: 'r and r2 :: 'r and \<delta>1 and
          domain2 and voters2 :: "'\<beta> \<Rightarrow> 'v set" and ballots2 :: "'\<beta> \<Rightarrow> 'b set" and 
          results2 :: "'\<beta> \<Rightarrow> 'r set" and aggregation2 \<delta>2

sublocale svg_power_comparison \<subseteq> 
  voting_power_comparison model_equivalence 
    S voters_svg "\<lambda>G. {b1, b2}" "\<lambda>G. {r1, r2}" "aggregation_method b1 b2 r1 r2" \<delta>1
    domain2 voters2 ballots2 results2 aggregation2 \<delta>2 
  by unfold_locales

end