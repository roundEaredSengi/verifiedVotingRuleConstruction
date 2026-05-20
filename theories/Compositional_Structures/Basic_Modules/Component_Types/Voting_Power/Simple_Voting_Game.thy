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

abbreviation voters_svg :: "'v Simple_Voting_Game \<Rightarrow> 'v set" where
  "voters_svg G \<equiv> fst G"

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

fun voter_isomorphism_SVG :: "('v \<Rightarrow> 'v) \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game" where
  "voter_isomorphism_SVG \<pi> (V, \<F>) = (\<pi> ` V, (image \<pi>) ` \<F>)"

fun svg_isomorphism :: 
  "('v \<Rightarrow> 'v) \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> bool" where
  "svg_isomorphism \<phi> G1 G2 = 
    (bij_betw \<phi> (voters_svg G1) (voters_svg G2) \<and> G2 = voter_isomorphism_SVG \<phi> G1)"

fun svg_meet :: "'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game" where
  "svg_meet G1 G2 = (voters_svg G1, coalitions G1 \<union> coalitions G2)"

fun svg_join :: "'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game" where
  "svg_join G1 G2 = (voters_svg G1, coalitions G1 \<inter> coalitions G2)"

section \<open>Simple Voting Games as a Voting Model\<close> 

\<comment> \<open>
  The simple voting game model represents voting systems via objects of type Simple_Voting_Game.
  Simple voting games represent binary decisions on two ballots and two results.
\<close>
locale simple_voting_game_model = 
  mod: voting_model S 
    voters_svg "\<lambda>G. {ballot1, ballot2}" "\<lambda>G. {result1, result2}" 
    "aggregation_method ballot1 ballot2 result1 result2" 
    for S :: "'v Simple_Voting_Game set" and
      ballot1 :: 'a and ballot2 :: 'a and result1 :: 'b and result2 :: 'b +
    assumes "result1 \<noteq> result2" and "ballot1 \<noteq> ballot2"

sublocale simple_voting_game_model \<subseteq> 
  voting_model S 
    fst "\<lambda>G. {ballot1, ballot2}" "\<lambda>G. {result1, result2}" 
    "aggregation_method ballot1 ballot2 result1 result2" 
  by unfold_locales

context simple_voting_game_model
begin

abbreviation "voters \<equiv> voters_svg"
abbreviation "ballots \<equiv> (\<lambda>G::('v Simple_Voting_Game). {ballot1, ballot2})"
abbreviation "results \<equiv> (\<lambda>G::('v Simple_Voting_Game). {result1, result2})"
abbreviation "aggregation \<equiv> 
  (aggregation_method::('a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> (('v \<Rightarrow> 'a) \<Rightarrow> 'b))) 
    ballot1 ballot2 result1 result2"

end

\<comment> \<open>
Models yes-no-decisions: 
Voters choose one out of True (= yes) and False (= no) and the result is True (= yes) iff
a winning coalition of voters chose yes, otherwise the result is False (= no).
\<close>
interpretation boolean_svg:
  simple_voting_game_model S True False True False
  by (unfold_locales, simp_all)

section \<open>Simple Voting Game Voting Power\<close>

locale svg_power = svg: simple_voting_game_model S b1 b2 r1 r2
  for S :: "'v Simple_Voting_Game set" and b1 :: 'b and b2 and r1 :: 'r and r2 +
  fixes
    \<delta> :: "('v Simple_Voting_Game, 'v) Voting_Power"
  assumes
    no_voter_no_power: "\<forall>a \<in> S. \<forall>v. v \<notin> fst a \<longrightarrow> \<delta> a v = 0"

sublocale svg_power \<subseteq> voting_power
  S fst "\<lambda>G. {b1, b2}" "\<lambda>G. {r1, r2}" "aggregation_method b1 b2 r1 r2" \<delta>
  by (unfold_locales, rule local.no_voter_no_power)

end