chapter \<open>Simple Voting Games\<close>

theory Simple_Voting_Game
  imports Voting_Power_Scratch

begin

section \<open>Voting Model\<close>

text \<open>
A simple voting game is a tuple consisting of a set (of voters) 
and a set family (of voter coalitions).
\<close>
type_synonym 'v Simple_Voting_Game = "'v set \<times> ('v set set)"

abbreviation voters_svg :: "'v Simple_Voting_Game \<Rightarrow> 'v set" where
  "voters_svg G \<equiv> fst G"

abbreviation coalitions :: "'v Simple_Voting_Game \<Rightarrow> 'v set set" where
  "coalitions G \<equiv> snd G"

fun monotone_SVG :: "'v Simple_Voting_Game \<Rightarrow> bool" where
  "monotone_SVG (V, \<F>) = (\<forall>S \<in> Pow V. \<forall>T \<in> Pow V. S \<subseteq> T \<longrightarrow> S \<in> \<F> \<longrightarrow> T \<in> \<F>)"

definition monotone_SVGs :: "'v Simple_Voting_Game set" where
  "monotone_SVGs \<equiv> Collect monotone_SVG"

section \<open>Voting Power Indices\<close>

fun swing_vote_svg :: "'v set set \<Rightarrow> 'v \<Rightarrow> 'v set \<Rightarrow> ereal" where
  "swing_vote_svg \<F> v S = (if ((S \<union> {v}) \<in> \<F>) \<noteq> ((S - {v}) \<in> \<F>) then 1 else 0)"

text \<open>
  First formulation of a Banzhaf index for simple voting games:
  Count the number of coalitions a voter can change by switching their vote and average over those.
\<close>
fun banzhaf_svg_1 :: "('v Simple_Voting_Game, 'v) Voting_Power" where
  "banzhaf_svg_1 (V, \<F>) v = (if infinite V then 0 else
    (1/(2^(card V))) * (\<Sum> S \<in> Pow V. swing_vote_svg \<F> v S))"
(* TODO: Original definition just assumes finite voter sets.
Formalizing the indices here forces one to explicitly think about infinite sets 
since every statement about the index includes infinite sets in its domain. 
Here, we define each voter's power to be 0 if V is infinite. *)

(* fun finite_test:: "nat set \<Rightarrow> bool" where
  "finite_test N = finite N"

value "finite {1::nat}" (* Zulip? *)
value "banzhaf_svg_1 ({1::nat, 2}, {{1}, {1,2}}) 1" *)

section \<open>Voting Power Properties\<close>

fun banzhaf_prob_svg :: "'v Simple_Voting_Game \<Rightarrow> 'v set measure" where
  "banzhaf_prob_svg G = uniform_count_measure (Pow (fst G))"

fun is_null_player :: "'v Simple_Voting_Game \<Rightarrow> 'v \<Rightarrow> bool" where
  "is_null_player (V, \<F>) v = (range (swing_vote_svg \<F> v) = {0})"

text \<open>
  A player is called null player if they do not have any swing votes.
  A voting power index satisfies the null player axiom if null players have 0 power in every SVG.
\<close>
fun null_player_axiom_svg_on :: "('v Simple_Voting_Game, 'v) Voting_Power_Axiom" where
  "null_player_axiom_svg_on \<G> \<delta> = 
    (\<forall>G \<in> \<G>. \<forall>v \<in> voters_svg G. is_null_player G v \<longrightarrow> \<delta> G v = 0)"

fun block_svg :: "'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> bool" where
  "block_svg G G' v w x = (
    x \<notin> voters_svg G \<and>
    voters_svg G' = voters_svg G - {v, w} \<union> {x} \<and> 
    coalitions G' = {S - {v, w} \<union> {x} |S. v \<in> S \<and> w \<in> S \<and> S \<in> coalitions G} \<union>
                    {S |S. v \<notin> S \<and> w \<notin> S \<and> S \<in> coalitions G}
  )"

(* TODO: Formulate axiom over all SVGs that have some merged voter instead of calculating block SVG *)
fun block_axiom_svg_on ::
  "('v Simple_Voting_Game, 'v) Voting_Power_Axiom" where
  "block_axiom_svg_on \<G> \<delta> = (\<forall>G \<in> \<G>. \<forall>v \<in> voters_svg G. \<forall>w \<in> voters_svg G. \<forall>x.
    (w \<noteq> v \<longrightarrow> (\<forall>G'. block_svg G G' v w x \<longrightarrow> (\<delta> G' x \<ge> Max{\<delta> G v, \<delta> G w}))))"

fun iso_svg :: 
  "('v \<Rightarrow> 'v) \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> 'v Simple_Voting_Game \<Rightarrow> bool" where
  "iso_svg \<phi> G1 G2 = 
    (bij_betw \<phi> (voters_svg G1) (voters_svg G2) \<and> (image \<phi>) ` (coalitions G1) = coalitions G2)"

fun symmetry_axiom_svg_on :: "('v Simple_Voting_Game, 'v) Voting_Power_Axiom" where
  "symmetry_axiom_svg_on \<G> \<delta> = 
    (\<forall>G1 \<in> \<G>. \<forall>G2 \<in> \<G>. \<forall>\<phi>. iso_svg \<phi> G1 G2 \<longrightarrow> (\<forall>v \<in> voters_svg G1. \<delta> G1 v = \<delta> G2 (\<phi> v)))"

section \<open>Property Proofs\<close>

lemma banzhaf_1_satisfies_null_player_axiom: 
  "null_player_axiom_svg_on UNIV banzhaf_svg_1"
proof (unfold null_player_axiom_svg_on.simps fst_def, safe)
  fix
    V :: "'a set" and
    \<F> :: "'a set set" and
    v :: 'a
  assume
    "v \<in> V" and "is_null_player (V, \<F>) v"
  hence "range (swing_vote_svg \<F> v) = {0}"
  by simp
  hence "\<forall>S. swing_vote_svg \<F> v S = 0"
    unfolding fst_def snd_def
    by fast
  hence "(\<Sum> S \<in> Pow V. swing_vote_svg \<F> v S) = 0"
    by simp
  thus "banzhaf_svg_1 (V, \<F>) v = 0"
    by simp
qed 

lemma banzhaf_1_satisfies_symmetry_axiom:
  "symmetry_axiom_svg_on UNIV banzhaf_svg_1"
  sorry

lemma banzhaf_1_satisfies_block_axiom: 
  "block_axiom_svg_on monotone_SVGs banzhaf_svg_1"
proof (simp only: block_axiom_svg_on.simps fst_def snd_def, safe, goal_cases)
  case (1 V \<F> v w x V' \<F>')
  hence merged_vot_set: "V' = V - {w, v} \<union> {x}"
    by auto
  from 1 show ?case
  proof (cases "finite V")
    case True
    let ?\<F> = "{S - {w} |S. (v \<in> S \<longleftrightarrow> w \<in> S) \<and> S \<in> \<F>}"
    let ?n = "card V"
    have "card V = Suc (card (V - {w}))"
      using 1 True card_Suc_Diff1
      by metis
    hence "1/(2^(card V)) = 1/(2 * 2^(card (V - {w})))" 
      by simp
    hence "2 * (1/(2^(card V))) = 2 * (1/(2 * 2^(card (V - {w}))))"
      by metis
    also have "... = 1/((2::ereal)^(card (V - {w})))"
      using True \<open>w \<in> V\<close>
      by (simp add: one_ereal_def) (* TODO why is this needed? *)
    finally have card1: "1/((2::ereal)^(card (V - {w}))) = (2::ereal) * (1/(2^(card V)))"
      by simp
    thus ?thesis (* TODO *)
      sorry
  next
    case False
    hence "infinite (V - {w, v})"
      by simp
    hence "infinite V'"
      using merged_vot_set
      by simp
    hence "banzhaf_svg_1 (V', \<F>') x = 0"
      by simp
    moreover have "Max {banzhaf_svg_1 (V, \<F>) v, banzhaf_svg_1 (V, \<F>) w} = 0"
      using False
      by simp
    ultimately show ?thesis  
      by order
  qed
qed

lemma banzhaf_1_is_prob_svg:
  fixes
    V :: "'v set" and
    \<F> :: "'v set set" and
    v :: 'v
  assumes
    "finite V" and "\<F> \<subseteq> Pow V" and "v \<in> V"
  shows
    "banzhaf_svg_1 (V, \<F>) v = emeasure (banzhaf_prob_svg (V, \<F>)) {S | S. swing_vote_svg \<F> v S = 1}"
proof -
  let ?swings = "{S | S. swing_vote_svg \<F> v S = 1}"
  have "\<forall>S. swing_vote_svg \<F> v S = 1 \<longrightarrow> S \<subseteq> V"
  proof (simp, safe)
    fix 
      S :: "'v set" and
      x :: 'v
    assume 
      "insert v S \<in> \<F>" and "x \<in> S"
    hence "S \<union> {v} \<subseteq> V"
      using assms(2)
      by blast
    thus "x \<in> V"
      using \<open>x \<in> S\<close>
      by blast
  next
    fix 
      S :: "'v set" and
      x :: 'v
    assume 
      "x \<in> S" and "x \<notin> V" and "S - {v} \<in> \<F>"
    hence "S - {v} \<subseteq> V"
      using assms(2)
      by blast
    hence "S \<subseteq> V"
      using assms(2) assms(3)
      by blast
    hence "x \<in> V"
      using \<open>x \<in> S\<close>
      by blast
    thus "False"
      using \<open>x \<notin> V\<close>
      by blast
  qed
  hence subset: "?swings \<subseteq> Pow V"
    by blast
  moreover have fin_pow: "finite (Pow V)"
    using assms(1)
    by simp
  ultimately have rewrite_prob:
    "emeasure (banzhaf_prob_svg (V, \<F>)) {S | S. swing_vote_svg \<F> v S = 1}
      = (card {S | S. swing_vote_svg \<F> v S = 1})/(card (Pow V))"
    unfolding banzhaf_prob_svg.simps
    using emeasure_uniform_count_measure[of "Pow V" ?swings]
    by simp
  have "ereal (1/(2^(card V))) = ereal (1/(card (Pow V)))"
    using assms(1) Power.card_Pow[of V, OF assms(1)]
    by simp
  hence 
    "\<forall>x::ereal. (1/(2^(card V))) * x = (1/(card (Pow V))) * x"
    by (metis ereal_divide ereal_power numeral_eq_ereal one_ereal_def power_eq_0_iff zero_neq_numeral)
  hence rewrite_pow':
    "(1/(2^(card V))) * (\<Sum> S \<in> Pow V. swing_vote_svg \<F> v S)
    = (1/(card (Pow V))) * (\<Sum> S \<in> Pow V. swing_vote_svg \<F> v S)"
    by simp

  have swing_vote: 
    "(\<lambda>S. (if swing_vote_svg \<F> v S = 1 then 1 else 0)) = (\<lambda>S. swing_vote_svg \<F> v S)"
    by auto
  have swings: "?swings = {S |S. S \<in> Pow V \<and> swing_vote_svg \<F> v S = 1}"
    using subset
    by blast

  hence "card ?swings = card {S |S. S \<in> Pow V \<and> swing_vote_svg \<F> v S = 1}"
    by simp
  also have 
    "... = (\<Sum>S\<in>Pow V. if swing_vote_svg \<F> v S = 1 then 1 else 0)"
    by (rule set_card[of "Pow V" "\<lambda>S. swing_vote_svg \<F> v S = 1", OF fin_pow])
  also have 
    "... = (\<Sum>S\<in>Pow V. swing_vote_svg \<F> v S)"
    using swing_vote
    sorry
  finally have
    "(\<Sum>S\<in>Pow V. swing_vote_svg \<F> v S) = card {S |S. swing_vote_svg \<F> v S = 1}"
    by simp
  hence rewrite_pow:
    "banzhaf_svg_1 (V, \<F>) v = (1/(card (Pow V))) * card {S | S. swing_vote_svg \<F> v S = 1}"
    using rewrite_pow'
    by simp
  thus ?thesis
    using rewrite_prob
    by simp
qed

section \<open>Code Generation and Stuff\<close>
value "card (X::(nat set))"

(* Why finite? *)


end