section \<open>Definition and Comparison of Voting Models\<close>

theory Voting_Models
  imports Electoral_Module
          "Games/Simple_Voting_Game"

begin

subsection \<open>Auxiliary Definitions\<close>

fun swap_args :: "('s \<Rightarrow> 't \<Rightarrow> 'r) \<Rightarrow> ('t \<Rightarrow> 's \<Rightarrow> 'r)" where
  "swap_args f = (\<lambda>t s. f s t)"

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
    f :: "('v \<Rightarrow> 'b) \<Rightarrow> 'o"
  assumes
    valid_outcomes: "\<forall>p::'v \<Rightarrow> 'b. p ` \<V> \<subseteq> \<B> \<longrightarrow> f p \<in> \<O>"

text \<open>
  A voting rule models the decision procedure of a voting system as the tallying method itself.
\<close>
locale voting_rule = voting_model \<V> \<B> \<O> \<F> \<F>
  for \<V> :: "'v set" and \<B> :: "'b set" and \<O> :: "'o set" and \<F> :: "('v \<Rightarrow> 'b) \<Rightarrow> 'o"
  (* TODO add assms? *)

sublocale voting_rule \<subseteq> voting_model \<V> \<B> \<O> \<F> \<F>
proof (rule local.voting_model_axioms) qed

locale rule\<^sub>e\<^sub>m =
  fixes 
    \<V> :: "'v set" and
    \<A> :: "'a set" and
    \<R> :: "'r set" and
    f :: "('a, 'v, 'r) Electoral_Module"
  assumes
    valid_results: "\<forall>p::('a, 'v) Profile. profile \<V> \<A> p \<longrightarrow> f \<V> \<A> p \<in> \<R>"
    (* curious:
      naming this valid_outcomes as well only leads to errors in interpretations, 
      not in the sublocale proof *)

sublocale rule\<^sub>e\<^sub>m \<subseteq> voting_rule \<V> "{rel. linear_order_on \<A> rel}" \<R> "\<lambda>p. f \<V> \<A> p"
proof (unfold_locales, simp add: image_subset_iff profile_def valid_results) qed 

text \<open>
  A simple voting game is a voting model for voting systems with binary decisions:
  Each voter chooses one out of two options, modelled as True and False and the result is
  the True-option iff the voters choosing it are 
\<close>
locale simple_voting_game = (* TODO model using 0, 1 instead of Booleans *)
  voting_model \<V> "UNIV::(bool set)" "UNIV::(bool set)" \<G> "\<lambda>p. value_fun \<G> (preimg p \<V> True)"
  for \<V> :: "'v set" and \<G> :: "'v Simple_Voting_Game" +
  assumes 
    valid_voters: "players \<G> = \<V>"

sublocale simple_voting_game \<subseteq> 
  voting_model \<V> "UNIV::(bool set)" "UNIV::(bool set)" \<G> "\<lambda>p. value_fun \<G> (preimg p \<V> True)" 
proof (unfold_locales) qed

interpretation majority_svg_5_voters:
  simple_voting_game "{1,2,3,4,5}" "({1,2,3,4,5}, \<lambda>S. card S \<ge> 3)"
proof (unfold_locales, simp_all) qed

end