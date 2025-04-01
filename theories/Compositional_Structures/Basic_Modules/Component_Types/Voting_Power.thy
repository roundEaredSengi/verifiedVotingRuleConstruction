section \<open>Voting Power\<close>

theory Voting_Power
  imports Electoral_Module
          Distance

begin

subsection \<open>Definition\<close>

text \<open>TODO: p1 and p2 should differ only in v's vote\<close>
fun swing_elections :: "('a, 'v, 'r) Electoral_Module \<Rightarrow> 'v \<Rightarrow> (('a, 'v) Election) rel" where
  "swing_elections f v = {(p1, p2). fun\<^sub>\<E> f p1 \<noteq> fun\<^sub>\<E> f p2}"

fun raw_power :: "'r Distance \<Rightarrow> ('a, 'v, 'r) Electoral_Module \<Rightarrow> 'v \<Rightarrow> ereal" where
  "raw_power d f v = (\<Sum> (p1, p2) \<in> swing_elections f v. d (fun\<^sub>\<E> f p1) (fun\<^sub>\<E> f p2))"

fun dist\<^sub>B\<^sub>Z :: "'r Distance" where
  "dist\<^sub>B\<^sub>Z x y = (if (x = y) then 0 else 1)"

text \<open>TODO: define base set for swing elections; nicer normalization factor...\<close>
fun banzhaf\<^sub>r\<^sub>a\<^sub>w :: "('a, 'v, 'r) Electoral_Module \<Rightarrow> 'v \<Rightarrow> ereal" where
  "banzhaf\<^sub>r\<^sub>a\<^sub>w f v = 
    (1/(ereal (card (well_formed_elections::(('a, 'v) Election set))))) 
      * (raw_power dist\<^sub>B\<^sub>Z f v)"
 
end