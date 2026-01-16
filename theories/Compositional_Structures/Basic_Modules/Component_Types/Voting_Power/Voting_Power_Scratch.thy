theory Voting_Power_Scratch
  imports "HOL-Library.Extended_Nonnegative_Real"
          "HOL-Probability.Probability_Measure"
          "../Voting_Models/Voting_Model_Scratch"

begin

fun characteristic :: "('x \<Rightarrow> 'y) \<Rightarrow> 'y set \<Rightarrow> 'x \<Rightarrow> nat" where
  "characteristic f Y x = (if f x \<in> Y then 1 else 0)"

section \<open>Simple Voting Games\<close>

fun swing_vote_svg :: "'v set set \<Rightarrow> 'v \<Rightarrow> 'v set \<Rightarrow> ereal" where
  "swing_vote_svg \<F> v S = (if ((S \<union> {v}) \<in> \<F>) \<noteq> ((S - {v}) \<in> \<F>) then 1 else 0)"

text \<open>
  First formulation of a Banzhaf index for simple voting games:
  Count the number of coalitions a voter can change by switching their vote and average over those.
\<close>
fun banzhaf_svg_1 :: "'v Simple_Voting_Game \<Rightarrow> 'v \<Rightarrow> ereal" where
  "banzhaf_svg_1 (V, \<F>) v = (1/(2^(card V))) * (\<Sum> S \<in> {S::'v set. S \<subseteq> V}. swing_vote_svg \<F> v S)"

fun banzhaf_prob_svg :: "'v Simple_Voting_Game \<Rightarrow> 'v set measure" where
  "banzhaf_prob_svg G = uniform_count_measure (Pow (fst G))"

lemma banzhaf_1_is_prob_svg:
  fixes
    V :: "'v set" and
    \<F> :: "'v set set" and
    v :: 'v
  assumes
    "finite V" and "\<F> \<subseteq> Pow V"
  shows
    "banzhaf_svg_1 (V, \<F>) v = emeasure (banzhaf_prob_svg (V, \<F>)) {S | S. swing_vote_svg \<F> v S = 1}"
proof -
  have "emeasure (banzhaf_prob_svg (V, \<F>)) {S | S. swing_vote_svg \<F> v S = 1}
        = (\<lambda>x. 1 / card (Pow V)) {S | S. swing_vote_svg \<F> v S = 1}"
    sorry
  thus ?thesis
    sorry
qed


section \<open>Voting Rules\<close>

fun differ_only_on :: "'v \<Rightarrow> ('v \<Rightarrow> 'b) \<Rightarrow> ('v \<Rightarrow> 'b) \<Rightarrow> bool" where
  "differ_only_on v p p' = (\<forall>x. p x \<noteq> p' x \<longrightarrow> x = v)"

fun swing_vote_rule :: "(('v \<Rightarrow> 'b) \<Rightarrow> 'r) \<Rightarrow> 'v \<Rightarrow> ('v \<Rightarrow> 'b) \<Rightarrow> ('v \<Rightarrow> 'b) \<Rightarrow> ereal" where
  "swing_vote_rule f v p p' = (if (differ_only_on v p p' \<and> f p \<noteq> f p') then 1 else 0)"

text \<open>
  First formulation of a Banzhaf index for voting rules:
  Count the number of profiles where the outcome would change if a voter changed their ballot
  while all other voters kept theirs, then average over all profiles.
\<close>
fun actual_funcset :: "'x set \<Rightarrow> 'y set \<Rightarrow> ('x \<Rightarrow> 'y) set" where
  "actual_funcset X Y = funcset X Y \<inter> extensional X"

fun banzhaf_rule_1 :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> 'v \<Rightarrow> ereal" where
  "banzhaf_rule_1 (V, B, R, f) v = 
    (1/(real ((card B)^(card V)))) * 
      (\<Sum> p \<in> actual_funcset V B. 
        Max {characteristic (swing_vote_rule f v p) {1} q | q. q \<in> actual_funcset V B})" 

(* Banzhaf index where probability interpretation breaks: *)
fun banzhaf_rule_2 :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> 'v \<Rightarrow> ereal" where
  "banzhaf_rule_2 (V, B, R, f) v = 
    (1/(real ((card B)^(card V)))) * 
      (\<Sum> p \<in> actual_funcset V B. \<Sum> q \<in> actual_funcset V B. (swing_vote_rule f v p q))" 
(* Additional danger of not stating the intended voting power measure
when formalizing with weird types: Almost wrote \<^latex>\<open>p \<in> UNIV\<close> here *)

term "prob_space"

fun banzhaf_prob_rule :: "('v, 'b, 'r) Voting_Rule \<Rightarrow> ('v \<Rightarrow> 'b) measure" where
  "banzhaf_prob_rule (V, B, R, f) = uniform_count_measure (actual_funcset V B)"

lemma banzhaf_1_is_prob_rule:
  fixes
    X :: "('v, 'b, 'r) Voting_Rule" and
    v :: 'v
  assumes
    "finite (voters X)" and "finite (ballots X)"
  shows
    "banzhaf_rule_1 X v = emeasure (banzhaf_prob_rule X) 
      {p | p. p \<in> actual_funcset (voters X) (ballots X) 
              \<and> (\<exists>q \<in> actual_funcset (voters X) (ballots X). swing_vote_rule (rule X) v p q = 1)}"
  sorry

(* The second Banzhaf definition does NOT yield a probability distribution
on any probability space on the set of ballot configurations. 
(I think, since the probability of the full space would have to be != 1.
May need additional assumptions about which events can be chosen per voter
- the above contradiction only works if some voter's event A equals the full space... *)
lemma banzhaf_2_is_not_prob_rule:
  fixes
    X :: "('v, 'b, 'r) Voting_Rule" and
    M :: "('v \<Rightarrow> 'b) measure"
  assumes
    "finite (voters X)" and 
    "finite (ballots X)" and 
    "prob_space M" and 
    "\<forall>v \<in> (voters X). \<exists>A \<in> sets M. banzhaf_rule_2 X v = emeasure M A"
  shows
    "False"
  sorry

section \<open>Strategic Games\<close>

text \<open>
  First formulation of a Banzhaf index for strategic games: TODO
\<close>
fun banzhaf_strat_1 :: "('v, 'a, 'r) Strategic_Game \<Rightarrow> 'v \<Rightarrow> ereal" where
  "banzhaf_strat_1 (V, R, A, P, f) v = 0" (* TODO *)
                     
end