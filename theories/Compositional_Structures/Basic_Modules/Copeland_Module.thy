(*  File:       Copeland_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Stephan Bohr, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Copeland Module\<close>

theory Copeland_Module
  imports "Component_Types/Elimination_Module"
begin

text \<open>
  This is the Copeland module used by the Copeland voting rule. The Copeland
  rule elects the alternatives with the highest difference between the amount
  of simple-majority wins and the amount of simple-majority losses. The module
  implemented herein only rejects the alternatives not elected by the voting
  rule, and defers the alternatives that would be elected by the full voting
  rule.
\<close>

subsection \<open>Definition\<close>

fun copeland_score :: "('a, 'v) Evaluation_Function" where
  "copeland_score V x A p =
    card {y \<in> A . wins V x p y} - card {y \<in> A . wins V y p x}"

fun copeland :: "('a, 'v, 'a Result) Electoral_Module" where
  "copeland V A p = max_eliminator copeland_score V A p"

subsection \<open>Soundness\<close>

theorem copeland_sound: "social_choice_result.electoral_module copeland"
  unfolding copeland.simps
  using max_elim_sound
  by metis

subsection \<open>Lemmas\<close>

text \<open>
  For a Condorcet winner w, we have: "card {y in A . wins x p y} = |A| - 1".
\<close>

lemma cond_winner_imp_win_count:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    w :: "'a"
  assumes "condorcet_winner V A p w"
  shows "card {a \<in> A. wins V w p a} = card A - 1"
proof -
  have "\<forall> a \<in> A - {w}. wins V w p a"
    using assms
    by auto
  hence "{a \<in> A - {w}. wins V w p a} = A - {w}"
    by blast
  hence winner_wins_against_all_others:
    "card {a \<in> A - {w}. wins V w p a} = card (A - {w})"
    by simp
  have "w \<in> A"
    using assms
    by simp
  hence "card (A - {w}) = card A - 1"
    using card_Diff_singleton assms
    by metis
  hence winner_amount_one: "card {a \<in> A - {w}. wins V w p a} = card (A) - 1"
    using winner_wins_against_all_others
    by linarith
  have win_for_winner_not_reflexive: "\<forall> a \<in> {w}. \<not> wins V a p a"
    by (simp add: wins_irreflex)
  hence "{a \<in> {w}. wins V w p a} = {}"
    by blast
  hence winner_amount_zero: "card {a \<in> {w}. wins V w p a} = 0"
    by simp
  have union:
    "{a \<in> A - {w}. wins V w p a} \<union> {x \<in> {w}. wins V w p x} = {a \<in> A. wins V w p a}"
    using win_for_winner_not_reflexive
    by blast
  have finite_defeated: "finite {a \<in> A - {w}. wins V w p a}"
    using assms
    by simp
  have "finite {a \<in> {w}. wins V w p a}"
    by simp
  hence "card ({a \<in> A - {w}. wins V w p a} \<union> {a \<in> {w}. wins V w p a}) =
          card {a \<in> A - {w}. wins V w p a} + card {a \<in> {w}. wins V w p a}"
    using finite_defeated card_Un_disjoint
    by blast
  hence "card {a \<in> A. wins V w p a} =
          card {a \<in> A - {w}. wins V w p a} + card {a \<in> {w}. wins V w p a}"
    using union
    by simp
  thus ?thesis
    using winner_amount_one winner_amount_zero
    by linarith
qed

text \<open>
  For a Condorcet winner w, we have: "card {y in A . wins y p x} = 0".
\<close>

lemma cond_winner_imp_loss_count:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    w :: "'a"
  assumes "condorcet_winner V A p w"
  shows "card {a \<in> A. wins V a p w} = 0"
  using Collect_empty_eq card_eq_0_iff insert_Diff insert_iff wins_antisym assms
  unfolding condorcet_winner.simps
  by (metis (no_types, lifting))

text \<open>
  Copeland score of a Condorcet winner.
\<close>

lemma cond_winner_imp_copeland_score:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    w :: "'a"
  assumes "condorcet_winner V A p w"
  shows "copeland_score V w A p = card A - 1"
proof (unfold copeland_score.simps)
  have "card {a \<in> A. wins V w p a} = card A - 1"
    using cond_winner_imp_win_count assms
    by metis
  moreover have "card {a \<in> A. wins V a p w} = 0"
    using cond_winner_imp_loss_count assms
    by (metis (no_types))
  ultimately show
    "enat (card {a \<in> A. wins V w p a} - card {a \<in> A. wins V a p w}) = enat (card A - 1)"
    by simp
qed

text \<open>
  For a non-Condorcet winner l, we have:
  "card {y in A . wins x p y} <= |A| - 1 - 1".
\<close>

lemma non_cond_winner_imp_win_count:
  fixes
    A :: "'a set" and
    V :: "'v set" and
    p :: "('a, 'v) Profile" and
    w :: "'a" and
    l :: "'a"
  assumes
    winner: "condorcet_winner V A p w" and
    loser: "l \<noteq> w" and
    l_in_A: "l \<in> A"
  shows "card {a \<in> A . wins V l p a} \<le> card A - 2"
proof -
  have "wins V w p l"
    using assms
    by auto
  hence "\<not> wins V l p w"
    using wins_antisym
    by simp
  moreover have "\<not> wins V l p l"
    using wins_irreflex
    by simp
  ultimately have wins_of_loser_eq_without_winner:
    "{y \<in> A . wins V l p y} = {y \<in> A - {l, w} . wins V l p y}"
    by blast
  have "\<forall> M f. finite M \<longrightarrow> card {x \<in> M . f x} \<le> card M"
    by (simp add: card_mono)
  moreover have "finite (A - {l, w})"
    using finite_Diff winner
    by simp
  ultimately have "card {y \<in> A - {l, w} . wins V l p y} \<le> card (A - {l, w})"
    using winner
    by (metis (full_types))
  thus ?thesis
    using assms wins_of_loser_eq_without_winner
    by (simp add: card_Diff_subset)
qed

subsection \<open>Property\<close>

text \<open>
  The Copeland score is Condorcet rating.
\<close>

theorem copeland_score_is_cr: "condorcet_rating copeland_score"
proof (unfold condorcet_rating_def, unfold copeland_score.simps, safe)
  fix
    A :: "'b set" and 
    V :: "'v set" and 
    p :: "('b, 'v) Profile" and 
    w :: 'b and 
    l :: 'b
  assume
    winner: "condorcet_winner V A p w" and
    l_in_A: "l \<in> A" and
    l_neq_w: "l \<noteq> w"
  hence "card {y \<in> A. wins V l p y} \<le> card A - 2"
    using non_cond_winner_imp_win_count
    by (metis (mono_tags, lifting))
  hence "card {y \<in> A. wins V l p y} - card {y \<in> A. wins V y p l} \<le> card A - 2"
    using diff_le_self order.trans
    by simp
  moreover have "card A - 2 < card A - 1"
    using card_0_eq card_Diff_singleton diff_less_mono2 empty_iff finite_Diff insertE
          insert_Diff l_in_A l_neq_w neq0_conv one_less_numeral_iff semiring_norm(76)
          winner zero_less_diff
    unfolding condorcet_winner.simps
    by metis
  ultimately have
    "card {y \<in> A. wins V l p y} - card {y \<in> A. wins V y p l} < card A - 1"
    using order_le_less_trans
    by fastforce
  moreover have "card {a \<in> A. wins V a p w} = 0"
    using cond_winner_imp_loss_count winner
    by metis
  moreover have "card A - 1 = card {a \<in> A. wins V w p a}"
    using cond_winner_imp_win_count winner
    by (metis (full_types))
  ultimately show
    "enat (card {y \<in> A. wins V l p y} - card {y \<in> A. wins V y p l}) <
      enat (card {y \<in> A. wins V w p y} - card {y \<in> A. wins V y p w})"
    using enat_ord_simps
    by simp
qed

theorem copeland_is_dcc: "defer_condorcet_consistency copeland"
proof (unfold defer_condorcet_consistency_def social_choice_result.electoral_module_def, safe)
  fix
    A :: "'b set" and 
    V :: "'a set" and
    p :: "('b, 'a) Profile"
  assume
    "finite A" and
    "finite V" and
    "profile V A p"
  hence "well_formed A (max_eliminator copeland_score V A p)"
    using max_elim_sound
    unfolding social_choice_result.electoral_module_def
    by metis
  thus "well_formed A (copeland V A p)"
    by auto
next
  fix
    A :: "'b set" and 
    V :: "'v set" and 
    p :: "('b, 'v) Profile" and 
    w :: 'b
  assume
    "condorcet_winner V A p w" and
    "finite A" and
    "finite V"
  moreover have "defer_condorcet_consistency (max_eliminator copeland_score)"
    by (simp add: copeland_score_is_cr)
  moreover have "\<forall> A V p. (copeland V A p = max_eliminator copeland_score V A p)"
    by simp
  ultimately show
    "copeland V A p = ({}, A - defer V copeland A p, {d \<in> A. condorcet_winner V A p d})"
    using Collect_cong
    unfolding defer_condorcet_consistency_def
    by (metis (no_types, lifting))
qed

end
