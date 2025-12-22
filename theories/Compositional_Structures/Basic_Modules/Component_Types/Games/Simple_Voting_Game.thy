section \<open>Simple Voting Games\<close>

theory Simple_Voting_Game
  imports Cooperative_Game
          "../Social_Choice_Types/Voting_Power"
          "HOL-Probability.Probability_Measure"

begin

subsection \<open>Simple Voting Games\<close>

type_synonym 'v Simple_Voting_Game = "'v set \<times> ('v set \<Rightarrow> bool)"

fun SVG_payoff :: "'v Simple_Voting_Game \<Rightarrow> ('v set \<Rightarrow> real)" where
  "SVG_payoff G S = (if (snd G S) then 1 else 0)"

fun players :: "'v Simple_Voting_Game \<Rightarrow> 'v set" where
  "players G = fst G"

fun winning :: "'v Simple_Voting_Game \<Rightarrow> ('v set \<Rightarrow> bool)" where
  "winning G = snd G"

type_synonym 'v SVG_Voting_Power_Domain = "'v Simple_Voting_Game \<times> 'v"

fun game :: "'v SVG_Voting_Power_Domain \<Rightarrow> 'v Simple_Voting_Game" where
  "game G = fst G"

fun player :: "'v SVG_Voting_Power_Domain \<Rightarrow> 'v" where
  "player G = snd G"

fun uncurry2 :: "('x \<Rightarrow> 'y \<Rightarrow> 'z) \<Rightarrow> (('x \<times> 'y) \<Rightarrow> 'z)" where
  "uncurry2 f = (\<lambda>(x,y). f x y)"

type_synonym 'v SVG_Voting_Power = "'v Simple_Voting_Game \<Rightarrow> 'v \<Rightarrow> ereal"

type_synonym 'v Uncurried_SVG_Voting_Power = "'v SVG_Voting_Power_Domain \<Rightarrow> ereal"

subsection \<open>Simple Voting Games as a Voting Model\<close>
                  
text \<open>
  A simple voting game is a voting model for voting systems with binary decisions:
  Each voter chooses one out of two options, modelled as True and False and the result is
  the True-option iff the voters choosing it are 
\<close>
locale simple_voting_game = voting_model where
    \<V> = \<V> and
    \<B> = "UNIV::(bool set)" and
    \<O> = "UNIV::(bool set)" and
    \<M> = \<M> and
    f = "\<lambda>p. winning \<M> (preimg p \<V> True)" and
    mech = mech
  for \<V> :: "'v set" and \<M> :: "'v Simple_Voting_Game" and 
    mech :: "('v, bool, bool, 'v Simple_Voting_Game) mechanisms" +
  assumes
    valid_voters: "players \<M> = \<V>"

sublocale simple_voting_game < voting_model where
  \<B> = "UNIV::bool set" and
  \<O> = "UNIV::bool set" and
  f = "\<lambda>p. winning \<M> (preimg p \<V> True)"
proof (unfold_locales) qed

fun swing_vote :: "'v Simple_Voting_Game \<Rightarrow> 'v \<Rightarrow> 'v set \<Rightarrow> bool" where
  "swing_vote G v S = (S \<subseteq> players G \<and> winning G (S \<union> {v}) \<noteq> winning G (S \<union> {v}))"

definition mech\<^sub>S\<^sub>V\<^sub>G :: "('v, bool, bool, 'v Simple_Voting_Game) mechanisms" where
  "mech\<^sub>S\<^sub>V\<^sub>G = 
    (|
      has_swing_vote = (\<lambda> G v. v \<in> players G \<and> (\<exists> S. swing_vote G v S)), 
      rename_model = (\<lambda> \<pi> G. (\<pi> ` (players G), (\<lambda> S. winning G {p \<in> players G. \<pi> p \<in> S})))
    |)" (* TODO official preimg function? *)

definition trivial_mech\<^sub>S\<^sub>V\<^sub>G :: "('v, bool, bool, 'v Simple_Voting_Game) mechanisms" where
  "trivial_mech\<^sub>S\<^sub>V\<^sub>G =
    (| has_swing_vote = (\<lambda> G v. True), rename_model = (\<lambda> \<pi> G. G) |)"

interpretation trivial_svg:
  simple_voting_game "{}" "({}, \<lambda>S. True)" trivial_mech\<^sub>S\<^sub>V\<^sub>G
proof (unfold_locales, simp_all) qed

interpretation majority_svg_5_voters:
  simple_voting_game "{1,2,3,4,5}" "({1,2,3,4,5}, \<lambda>S. card S \<ge> 3)" mech\<^sub>S\<^sub>V\<^sub>G
proof (unfold_locales, simp_all) qed 
 
(*
  TODO won't be able to show that?
  There should be counterexamples in the current implementation - fix that!
lemma rule_svg_isomorphism:
  fixes
    \<V> :: "'v set" and
    \<F> :: "('v \<Rightarrow> bool) \<Rightarrow> bool" and
    \<G> :: "'v Simple_Voting_Game" and
    f :: "('v \<Rightarrow> bool) \<Rightarrow> bool" and
    mech :: "('v, bool, bool, ('v \<Rightarrow> bool) \<Rightarrow> bool) mechanisms" and
    mech' :: "('v, bool, bool, 'v Simple_Voting_Game) mechanisms" and
    iso :: "(('v \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> bool"
  assumes
    rule: "voting_rule \<V> UNIV UNIV \<F>" and
    svg: "simple_voting_game \<V> \<G>" and
    iso: "model_isomorphism \<V> UNIV UNIV \<F> \<G> f mech mech' iso"
  shows
    rule_is_tally: "f = \<F>" and 
    tally_is_svg: "f = (\<lambda>p. winning \<G> (preimg p \<V> True))"
proof (simp_all)
  from iso rule show "f = \<F>"
    unfolding model_isomorphism_def model_isomorphism_axioms_def
  sorry
*)

subsection \<open>Voting Power on Simple Voting Games\<close>

fun \<delta>\<^sub>B\<^sub>Z :: "('v, 'v Simple_Voting_Game) Voting_Power" where
  "\<delta>\<^sub>B\<^sub>Z G v = 
    (1/2^(card (players G))) 
      * (real (card (preimg (swing_vote G v) {S. S \<subseteq> players G} True)))"
 
fun tally\<^sub>S\<^sub>V\<^sub>G :: "'v Simple_Voting_Game \<Rightarrow> (('v \<Rightarrow> bool) \<Rightarrow> bool)" where
  "tally\<^sub>S\<^sub>V\<^sub>G \<G> p = winning \<G> (preimg p (players \<G>) True)"

fun all_svgs :: "'v set \<Rightarrow> ('v Simple_Voting_Game \<times> (('v \<Rightarrow> bool) \<Rightarrow> bool)) set" where
  "all_svgs V = {((V, vf), tally\<^sub>S\<^sub>V\<^sub>G (V, vf)) | vf. simple_voting_game V (V, vf)}"

lemma classic_svg_banzhaf_on_all_svgs_of_a_voter_set:
  fixes
    \<V> :: "'v set"
  assumes
    fin: "finite \<V>"
  shows
    "banzhaf_index \<V> (UNIV::(bool set)) (UNIV::(bool set)) (all_svgs \<V>) \<delta>\<^sub>B\<^sub>Z mech\<^sub>S\<^sub>V\<^sub>G" 
proof (unfold_locales, simp_all, safe)
  fix
    \<w> :: "'v set \<Rightarrow> bool"
  show "voting_model \<V> UNIV UNIV (tally\<^sub>S\<^sub>V\<^sub>G (\<V>, \<w>))"
    using voting_model_def
    by blast
next
  fix
    \<pi> :: "'v \<Rightarrow> 'v" and
    V :: "'v set" and
    \<w> :: "'v set \<Rightarrow> bool" and
    v :: 'v
  assume
    "\<pi> \<in> Bij \<V>" and
    "simple_voting_game \<V> (\<V>, \<w>)" and
    "v \<in> \<V>"
  obtain V' :: "'v set" and \<w>' :: "'v set \<Rightarrow> bool" where
    img: "(V', \<w>') = rename_model mech\<^sub>S\<^sub>V\<^sub>G \<pi> (\<V>, \<w>)"
    by (simp add: mech\<^sub>S\<^sub>V\<^sub>G_def)
  have players: "players (\<V>, \<w>) = \<V>"
    by simp
  with img have "V' = \<pi> ` \<V>"
    by (simp add: mech\<^sub>S\<^sub>V\<^sub>G_def)
  also have "\<pi> ` \<V> = \<V>"
    using \<open>\<pi> \<in> Bij \<V>\<close>
    unfolding Bij_def bij_betw_def
    by blast
  finally have "V' = \<V>"
    by simp
  moreover have "simple_voting_game \<V> (\<V>, \<w>')"
    unfolding simple_voting_game_def voting_model_def simple_voting_game_axioms_def
    by simp
  ultimately show 
    "\<exists>\<w>'. rename_model mech\<^sub>S\<^sub>V\<^sub>G \<pi> (\<V>, \<w>) = (\<V>, \<w>') \<and> 
      Simple_Voting_Game.simple_voting_game \<V> (\<V>, \<w>')"
    using img
    by metis
qed

end