theory Banzhaf_Index
  imports Simple_Voting_Game_Comparison

begin


section \<open>Banzhaf Index Definitions\<close>

(* TODO definition of swing votes is now in 3 places, don't *)
fun swing_vote_svg :: "'v set set \<Rightarrow> 'v \<Rightarrow> 'v set \<Rightarrow> ereal" where
  "swing_vote_svg \<F> v S = (if ((S \<union> {v}) \<in> \<F>) \<noteq> ((S - {v}) \<in> \<F>) then 1 else 0)"

text \<open>
  First formulation of a Banzhaf index for simple voting games:
  Count the number of coalitions a voter can change by switching their vote and average over those.
\<close>
fun banzhaf_svg_1 :: "('v Simple_Voting_Game, 'v) Voting_Power" where
  "banzhaf_svg_1 (V, \<F>) v = (if v \<notin> V \<or> infinite V then 0 else
    (1/(2^(card V))) * (\<Sum> S \<in> Pow V. swing_vote_svg \<F> v S))"
(* TODO: Original definition just assumes finite voter sets.
Formalizing the indices here forces one to explicitly think about infinite sets 
since every statement about the index includes infinite sets in its domain. 
Here, we define each voter's power to be 0 if V is infinite. *)

section \<open>Banzhaf Voting Power Index\<close>

(* 
Banzhaf Index is axiomatized on monotone SVGs by:
- symmetry
- null player
- total power
- transfer
*)

text \<open>
We may call a voting power index a Banzhaf index if it satisfies the extended formulation
of the simple voting game Banzhaf index axiomatization.
\<close>
locale banzhaf_index_axioms =
  symmetry_axiom domain voters ballots results aggregation \<delta> +
  null_player_axiom domain voters ballots results aggregation \<delta> + 
  transfer_axiom domain voters ballots results aggregation \<delta> +
  total_power_axiom domain voters ballots results aggregation \<delta> swings
  (* TODO total power axiom *)
  for \<delta> and domain :: "'\<alpha> set" and results :: "'\<alpha> \<Rightarrow> 'r set" and 
    voters :: "'\<alpha> \<Rightarrow> 'v set" and ballots aggregation swings
  (* No additional assumptions since the combined assumptions of the property locales suffice *)

text \<open>
We may call a voting power index a Banzhaf index if it measures the probability of TODO.
\<close>
locale banzhaf_index_probability = ipower domain voters ballots results aggregation \<delta> space 
  for domain :: "'\<alpha> set" and voters :: "'\<alpha> \<Rightarrow> 'v set" and ballots :: "'\<alpha> \<Rightarrow> 'b set" and
    results :: "'\<alpha> \<Rightarrow> 'r set" and aggregation :: "'\<alpha> \<Rightarrow> ('v, 'b, 'r) Aggregation_Method" and 
    \<delta> and space +
  assumes
    "True" (* TODO assume Gleichverteilung or assume swing probability? *)

text \<open>
We may call a voting power index a Banzhaf index if, in situations that can be modelled as 
simple voting games, it behaves like the original Banzhaf index on simple voting games.
\<close>
locale banzhaf_index_comparison = comp: svg_power_comparison 
  model_equivalence S b1 b2 r1 r2 banzhaf_svg_1 domain voters ballots results aggregation \<delta>
  for model_equivalence and S and b1 and b2 and r1 and r2 and domain :: "'\<alpha> set" and 
    voters :: "'\<alpha> \<Rightarrow> 'v set" and ballots :: "'\<alpha> \<Rightarrow> 'b set" and results :: "'\<alpha> \<Rightarrow> 'r set" and 
    aggregation :: "'\<alpha> \<Rightarrow> ('v, 'b, 'r) Aggregation_Method" and \<delta> +
  assumes
    "comp.power_equality"

section \<open>Simple Voting Game Banzhaf Index\<close>

context simple_voting_game_model
begin 

(* TODO how to "term "model.voting_setups""? *)

subsection \<open>Swing Votes\<close>

fun svg_swings :: "'v Simple_Voting_Game \<Rightarrow> 'v \<Rightarrow> ('v \<Rightarrow> 'a) set" where
  "svg_swings (V, \<F>) v = {svg_profile (V, \<F>) X | X. X \<subseteq> V \<and> ((X \<union> {v}) \<in> \<F>) \<noteq> ((X - {v}) \<in> \<F>)}"

definition svg_swing_space :: "('v Simple_Voting_Game \<times> 'v) measure" where
  "svg_swing_space = Abs_measure (\<Omega>::('v Simple_Voting_Game \<times> 'v) set, A, \<mu>)" (* TODO *)

fun meet_res :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" where
  "meet_res x y = (if result1 \<in> {x, y} then result1 else x)"

fun join_res :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" where
  "join_res x y = (if result2 \<in> {x, y} then result2 else x)"

subsection \<open>Axioms\<close>

interpretation symmetry_satisfied:
  symmetry_axiom 
    S svg_voters svg_ballots svg_results svg_aggregation banzhaf_svg_1 voter_isomorphism_SVG
proof (unfold_locales, safe)
  fix V :: "'v set" and \<F> :: "'v set set" and v :: 'v
  assume 
    non_voter: "v \<notin> fst (V, \<F>)"
  thus "banzhaf_svg_1 (V, \<F>) v = 0"
    by simp
next
  fix V :: "'v set" and \<F> :: "'v set set" and 
      V' :: "'v set" and \<F>' :: "'v set set" and 
      \<sigma> :: "'v \<Rightarrow> 'v" and p :: "('v, 'a) Profile"
  assume
    "(V, \<F>) \<in> S" and "(V', \<F>') \<in> S" and prof: "p \<in> mod.profiles (V', \<F>')" and
    bij: "bij_betw \<sigma> (fst (V, \<F>)) (fst (V', \<F>'))" and
    iso: "(V', \<F>') = voter_isomorphism_SVG \<sigma> (V, \<F>)"
  hence rewrite_vot: "V' = \<sigma> ` V"
    unfolding svg_isomorphism.simps
    by (simp add: bij_betw_def)
  have rewrite_coal: "\<F>' = (image \<sigma>) ` \<F>"
    using iso
    by simp
  have "aggregation_method ballot1 ballot2 result1 result2 (V, \<F>) (p \<circ> \<sigma>) =
    (if (preimg_in V (p \<circ> \<sigma>) {ballot1} \<in> \<F>) then result1 else result2)"
    by simp
  also have "... = (if (preimg_in V' p {ballot1} \<in> \<F>') then result1 else result2)" 
    using rewrite_vot rewrite_coal
    sorry
  finally show
    "aggregation_method ballot1 ballot2 result1 result2 (V, \<F>) (p \<circ> \<sigma>) =
       aggregation_method ballot1 ballot2 result1 result2 (V', \<F>') p"
    by simp
next
  fix V :: "'v set" and \<F> :: "'v set set" and 
      V' :: "'v set" and \<F>' :: "'v set set" and 
      \<sigma> :: "'v \<Rightarrow> 'v" and v :: 'v
  assume 
    "(V, \<F>) \<in> S" and "(V', \<F>') \<in> S" and vot: "mod.valid_voter (V, \<F>) v" and
    bij: "bij_betw \<sigma> (fst (V, \<F>)) (fst (V', \<F>'))" and
    iso: "(V', \<F>') = voter_isomorphism_SVG \<sigma> (V, \<F>)"
  hence rewrite_vot: "V' = \<sigma> ` V"
    unfolding svg_isomorphism.simps
    by (simp add: bij_betw_def)
  have rewrite_coal: "\<F>' = (image \<sigma>) ` \<F>"
    using iso
    by simp
  thus "banzhaf_svg_1 (V, \<F>) v = banzhaf_svg_1 (V', \<F>') (\<sigma> v)"
    sorry
qed

(* TODO 
have to instantiate lattice class with {ballot1, ballot2} if we use the type class,
requires types to sets? 
interpretation simple_voting_game_banzhaf_axioms:
  banzhaf_index_axioms voter_isomorphism_SVG svg_meet svg_join banzhaf_svg_1 
    S results voters ballots aggregation svg_swings
  sorry
*)

interpretation simple_voting_game_banzhaf_axioms:
  banzhaf_index_axioms voter_isomorphism_SVG svg_meet svg_join meet_res join_res 
    banzhaf_svg_1 S svg_results svg_voters svg_ballots svg_aggregation svg_swings
  sorry

subsection \<open>I-Power\<close>

interpretation simple_voting_game_banzhaf_probability:
  banzhaf_index_probability 
    S svg_voters svg_ballots svg_results svg_aggregation banzhaf_svg_1 svg_swing_space
  sorry

subsection \<open>Simple Voting Game Equality\<close>

interpretation svg_comp: 
  svg_power_comparison "(=)" S ballot1 ballot2 result1 result2 
    banzhaf_svg_1 S svg_voters svg_ballots svg_results svg_aggregation banzhaf_svg_1
  by (unfold_locales, simp_all, rule local.symmetry_satisfied.no_voter_no_power)

text \<open>
A trivial Banzhaf index that coincides with the Banzhaf index on simple voting games is the
Banzhaf index on simple voting games itself.
\<close>
interpretation simple_voting_game_banzhaf_equality:
  banzhaf_index_comparison 
    "(=)" S ballot1 ballot2 result1 result2 
    S svg_voters svg_ballots svg_results svg_aggregation banzhaf_svg_1
  by (unfold_locales, safe, simp_all, unfold svg_comp.power_equality_def, simp)
                                                                                       
end

end