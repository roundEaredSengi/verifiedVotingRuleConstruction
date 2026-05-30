chapter \<open>Simple Voting Games\<close>

theory Simple_Voting_Game
  imports Voting_Model
          Voting_Power

begin                           

section \<open>Simple Voting Game Definition\<close>

text \<open>
A simple voting game is a tuple consisting of a set (of voters) 
and a set family (of voter coalitions).
\<close>
type_synonym 'v Simple_Voting_Game = "'v set \<times> ('v set set)"

abbreviation coalitions :: "'v Simple_Voting_Game \<Rightarrow> 'v set set" where
  "coalitions G \<equiv> snd G"  

fun aggregation_method :: 
  "'b \<Rightarrow> 'b \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> (('v \<Rightarrow> 'b) \<Rightarrow> 'r)" where
  "aggregation_method ball1 ball2 res1 res2 (V, \<F>) p = 
    (if (preimg_in V p {ball1} \<in> \<F>) then res1 else res2)" (* TODO require p to be valid *)

fun monotone_SVG :: "'v Simple_Voting_Game \<Rightarrow> bool" where
  "monotone_SVG (V, \<F>) = (\<forall>S \<in> Pow V. \<forall>T \<in> Pow V. S \<subseteq> T \<longrightarrow> S \<in> \<F> \<longrightarrow> T \<in> \<F>)"

definition monotone_SVGs :: "'v Simple_Voting_Game set" where
  "monotone_SVGs \<equiv> Collect monotone_SVG"

section \<open>Simple Voting Game Transformations\<close>

fun svg_isomorphism :: "('v \<Rightarrow> 'v) \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game" where
  "svg_isomorphism \<pi> (V, \<F>) = (\<pi> ` V, (image \<pi>) ` \<F>)"

fun svg_meet :: "'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game" where
  "svg_meet G1 G2 = (fst G1, coalitions G1 \<union> coalitions G2)"

fun svg_join :: "'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game" where
  "svg_join G1 G2 = (fst G1, coalitions G1 \<inter> coalitions G2)"

section \<open>Simple Voting Games as a Voting Model\<close> 

fun svg_rule :: 
  "'b \<Rightarrow> 'b \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> ('v Simple_Voting_Game, 'v, 'b, 'r) Voting_Rule_Transformation" where
  "svg_rule b1 b2 r1 r2 (V, \<F>) = (V, {b1, b2}, {r1, r2}, aggregation_method b1 b2 r1 r2 (V, \<F>))"

\<comment> \<open>
  The simple voting game model represents voting systems via objects of type Simple_Voting_Game.
  Simple voting games represent binary decisions on two ballots and two results.
\<close>
locale simple_voting_game_model = 
  mod: voting_model S "svg_rule ballot1 ballot2 result1 result2"
    for S :: "'v Simple_Voting_Game set" and
      ballot1 :: 'a and ballot2 :: 'a and result1 :: 'b and result2 :: 'b +
    assumes "result1 \<noteq> result2" and "ballot1 \<noteq> ballot2" and "\<forall>G \<in> S. snd G \<subseteq> Pow (mod.voters G)"

sublocale simple_voting_game_model \<subseteq> 
  voting_model S "svg_rule ballot1 ballot2 result1 result2"
  by unfold_locales

context simple_voting_game_model
begin

abbreviation "svg_voters \<equiv> rule_voters \<circ> (svg_rule ballot1 ballot2 result1 result2)"
lemma svg_voters_fst [simp]: "svg_voters = fst"
  by auto

abbreviation "svg_ballots \<equiv> rule_ballots \<circ> (svg_rule ballot1 ballot2 result1 result2)"
abbreviation "svg_results \<equiv> rule_results \<circ> (svg_rule ballot1 ballot2 result1 result2)"
abbreviation "svg_aggregation \<equiv> rule \<circ> (svg_rule ballot1 ballot2 result1 result2)"

fun svg_profile :: "'v Simple_Voting_Game \<Rightarrow> 'v set \<Rightarrow> ('v, 'a) Profile" where
  "svg_profile (V, \<F>) X = (\<lambda>v. (if v \<in> X then ballot1 else ballot2))"

end

\<comment> \<open>
Models yes-no-decisions: 
Voters choose one out of True (= yes) and False (= no) and the result is True (= yes) iff
a winning coalition of voters chose yes, otherwise the result is False (= no).
\<close>
interpretation boolean_svg:
  simple_voting_game_model S True False True False
proof (unfold_locales, unfold Let_def, simp_all, safe)
  fix V :: "'a set" and \<F> :: "'a set set" and p :: "('a, bool) Profile"
  assume "p \<in> rule_voters (svg_rule True False True False (V, \<F>)) 
                \<rightarrow> rule_ballots (svg_rule True False True False (V, \<F>))"
  hence "rule (svg_rule True False True False (V, \<F>)) p \<in> {True, False}"
    by simp
  thus "rule (svg_rule True False True False (V, \<F>)) p
          \<in> rule_results (svg_rule True False True False (V, \<F>))"
    by simp
qed

section \<open>Simple Voting Game Voting Power\<close>

locale svg_power = svg: simple_voting_game_model S b1 b2 r1 r2
  for S :: "'v Simple_Voting_Game set" and b1 :: 'b and b2 and r1 :: 'r and r2 +
  fixes
    \<delta> :: "('v Simple_Voting_Game, 'v) Voting_Power"
  assumes
    no_voter_no_power: "\<forall>a \<in> S. \<forall>v. v \<notin> fst a \<longrightarrow> \<delta> a v = 0"

sublocale svg_power \<subseteq> voting_power S "svg_rule b1 b2 r1 r2" \<delta>
proof (unfold_locales)
  have "\<forall>a. rule_voters (svg_rule b1 b2 r1 r2 a) = fst a"
    by simp
  thus "\<forall>a\<in>S. \<forall>v. v \<notin> rule_voters (svg_rule b1 b2 r1 r2 a) \<longrightarrow> \<delta> a v = 0"
    using local.no_voter_no_power
    by metis
qed

end