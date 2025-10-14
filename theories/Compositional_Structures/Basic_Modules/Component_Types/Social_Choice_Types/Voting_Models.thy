section \<open>Definition and Comparison of Voting Models\<close>

theory Voting_Models
  imports Main

begin

subsection \<open>Voting Models\<close>

text \<open>
  A voting model is a formalization of a voting system.
  Any voting model, one way or another, should model the collective decision carried out through
  a voting model via its...
    - eligible voters \<V>
    - decisions/ballots \<B> that the voters decide upon
    - potential election outcomes \<O>
    - representation \<M> of the decision process itself
    - tallying method that, based on the decision procedure and
        valid decisions in \<B> made by all voters \<V>, yield an election outcome \<O>

  Note that a specific tallying method is just one interpretation of a voting model's components.
  There may be other sensible interpretations of the same or similar structures. For instance,
  a simple voting game may be interpreted as binary decision between 2 alternatives with a single
  winner, or with potentially tied winners. 
  As another instance, the decision process may be 
  described in arbitrary detail by letting the voters choose both public and private options
  while the tallying method still considers only the public choices.
\<close> 
locale voting_model = 
  fixes 
    \<V> :: "'v set" and
    \<B> :: "'b set" and
    \<O> :: "'o set" and
    \<M> :: "'x" and 
      (* 
        \<M> is the mathematical structure representing the decision process.
        It may contain details that are ultimately irrelevant to the tallying method.
      *)
    f :: "('v \<Rightarrow> 'b) \<Rightarrow> 'o" 
      (* Intuitively, f describes the core of \<M> as a decision process. *)
  assumes
    valid_outcomes: "\<forall> p::'v \<Rightarrow> 'b. p ` \<V> \<subseteq> \<B> \<longrightarrow> f p \<in> \<O>"

text \<open>
  A voting rule models the decision procedure of a voting system as the tallying method itself.
\<close>
locale voting_rule = voting_model \<V> \<B> \<O> \<F> \<F>
  for \<V> :: "'v set" and \<B> :: "'b set" and \<O> :: "'o set" and \<F> :: "('v \<Rightarrow> 'b) \<Rightarrow> 'o"
  (* TODO add assms? *)

sublocale voting_rule \<subseteq> voting_model \<V> \<B> \<O> \<F> \<F>
proof (rule local.voting_model_axioms) qed

subsection \<open>Comparison of Voting Models\<close>

text \<open>
  For two voting models with different descriptions \<M>, \<M>' of the decision process
  to be isomorphic, the voters, ballots, outcomes and tallying method necessarily need to be equal.
  Further requirements about isomorphism of \<M>, \<M>' can be added.
\<close>
(* 
  TODO too strict, only require bijections instead of identity between all components but \<M>, \<M>'?  
*)
locale model_isomorphism = 
  m1: voting_model \<V> \<B> \<O> \<M> f + m2: voting_model \<V> \<B> \<O> \<M>' f
  for 
    \<V> :: "'v set" and
    \<B> :: "'b set" and
    \<O> :: "'o set" and
    \<M> :: "'x" and \<M>' :: "'y" and
    f :: "('v \<Rightarrow> 'b) \<Rightarrow> 'o" +
  fixes 
    isomorphism :: "'x \<Rightarrow> 'y \<Rightarrow> bool"
  assumes
    "isomorphism \<M> \<M>'"


locale model_set_isomorphism =
  fixes   
    \<V> :: "'v set" and
    \<B> :: "'b set" and
    \<O> :: "'o set" and
    \<M> :: "('x \<times> (('v \<Rightarrow> 'b) \<Rightarrow> 'o)) set" and
    \<M>' :: "('y \<times> (('v \<Rightarrow> 'b) \<Rightarrow> 'o)) set" and
    isomorphism :: "'x \<Rightarrow> 'y \<Rightarrow> bool"
  assumes
    correspondence\<^sub>r: (* implies being a voting_model *)
      "\<forall> (m, f) \<in> \<M>. \<exists> m'. (m', f) \<in> \<M>' \<and> model_isomorphism \<V> \<B> \<O> m m' f isomorphism" and
    correspondence\<^sub>l: (* implies being a voting_model *)
      "\<forall> (m', f) \<in> \<M>'. \<exists> m. (m, f) \<in> \<M> \<and> model_isomorphism \<V> \<B> \<O> m m' f isomorphism" and
    occurrence:
      "\<forall> m::'x. \<forall> m'::'y. \<forall>f. 
        model_isomorphism \<V> \<B> \<O> m m' f isomorphism \<longrightarrow> ((m,f) \<in> \<M> \<longleftrightarrow> (m', f) \<in> \<M>')"

subsection \<open>Exemplary Instantiations\<close>

text \<open> 
  Any voting model is isomorphic to itself if decision processes are required to be identical.
\<close>
lemma self_isomorphism:
  fixes
    \<V> :: "'v set" and
    \<B> :: "'b set" and
    \<O> :: "'o set" and
    \<M> :: "'x" and
    f :: "('v \<Rightarrow> 'b) \<Rightarrow> 'o"
  assumes
    "voting_model \<V> \<B> \<O> f"
  shows
    "model_isomorphism \<V> \<B> \<O> \<M> \<M> f (\<lambda>x y. x = y)"
proof (unfold_locales, simp_all)
  show "\<forall>p. p ` \<V> \<subseteq> \<B> \<longrightarrow> f p \<in> \<O>"
    using assms
    unfolding voting_model_def
    by blast
qed

end