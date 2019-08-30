theory Kongruencije
  imports Main HOL.Real
begin


(* Neka je m prirodni broj veci od 1. Kazemo da su brojevi a, b \<in> Z kongruentni po modulu m
i pisemo a \<equiv> b (mod m) ili a \<equiv>m b ako  m | (a − b) . *)
definition kongruentni_po_modulu :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool"  where
"kongruentni_po_modulu a b m = ((m > 1) \<and> (m dvd (a - b)))"


(* Tvrdjenje 1:  Ako je a \<equiv> a1 (mod m) i b \<equiv> b1 (mod m) onda je:
    a + b \<equiv> a1 + b1 (mod m)
    a * b \<equiv> a1 * b1 (mod m)
 *)
lemma tvrdjenje_1_1:
  assumes "m > 1"
  assumes "kongruentni_po_modulu a a1 m"
  assumes "kongruentni_po_modulu b b1 m"
  shows "kongruentni_po_modulu (a + b) (a1 + b1) m" 
  unfolding kongruentni_po_modulu_def
proof-
  have *: "m dvd (a - a1)"
    using assms(1) assms(2)
    using kongruentni_po_modulu_def 
    by simp
  have **: "m dvd (b - b1)"
    using assms(1) assms(3)
    using kongruentni_po_modulu_def 
    by simp
  have "m dvd ((a - a1) + (b - b1))"
    using * **
    by simp
  hence "m dvd (a + b) - (a1 + b1)"
    by (simp add: algebra_simps)
  thus "(m > 1) \<and> (m dvd (a + b) - (a1 + b1))"
      using assms(1)
      by simp
  qed

lemma tvrdjenje_1_2:
  assumes "m > 1"
  assumes "kongruentni_po_modulu a a1 m"
  assumes "kongruentni_po_modulu b b1 m"
  shows "kongruentni_po_modulu (a * b) (a1 * b1) m" 
  unfolding kongruentni_po_modulu_def
proof-
  have "m dvd (a - a1)"
    using assms(1) assms(2)
    using kongruentni_po_modulu_def 
    by simp
  hence *:"m dvd (a - a1)*b"
    by simp
  have "m dvd (b - b1)"
    using assms(1) assms(3)
    using kongruentni_po_modulu_def 
    by simp
  hence **:"m dvd a1*(b - b1)"
    by simp
  have "m dvd ((a - a1)*b + a1*(b - b1))"
    using * **
    by simp
  hence "m dvd (a*b - a1*b1)"
    by (simp add: algebra_simps)
  thus "(m > 1) \<and> (m dvd (a*b - a1*b1))"
    using assms(1)
    by simp
qed


(* Tvrdjenje 2:  Ako je a \<equiv> a1 (mod m) i k je prirodan broj, onda je a^k \<equiv> a1^k (mod m) *)
lemma tvrdjenje_2:
  fixes k :: nat
  assumes "m > 1"
  assumes "kongruentni_po_modulu a a1 m"
  shows "kongruentni_po_modulu (a^k) (a1^k) m"
 (* unfolding kongruentni_po_modulu_def *)
proof (induction k)
  case 0
  then show ?case
    unfolding kongruentni_po_modulu_def
    using assms
    by simp
 next
  case (Suc k)
  then show ?case
  proof-
    thm assms
    thm Suc
    have "kongruentni_po_modulu (a^k * a) (a1^k * a1) m"
      using assms Suc
      by (simp add: tvrdjenje_1_2)
    hence "kongruentni_po_modulu ((a^(k+1))) ((a1^(k+1))) m"
      by (simp add: algebra_simps)
    thus ?case
      using assms
      by simp
    qed
  qed


(* Tvrdjenje 3:  \<equiv>m je relacija ekvivalencije *)
(* Relacija je relacija ekvivalencije ako je refleksivna, simetricna i tranzitivna.*)

lemma refleksivna: 
  assumes "m > 1"
  shows "kongruentni_po_modulu a a m"
unfolding kongruentni_po_modulu_def
proof-
  have "m dvd (a - a)"
    by simp
  thus "(m > 1) \<and> (m dvd (a - a))"
    using assms
    by simp
qed


lemma simetricna:
  assumes "m > 1"
  assumes "kongruentni_po_modulu x y m"
  shows "kongruentni_po_modulu y x m"
unfolding kongruentni_po_modulu_def
proof-
  have "m dvd (x - y)"
    using assms
    unfolding kongruentni_po_modulu_def
    by simp
  hence "m dvd (y - x)"
    by (simp add: dvd_diff_commute)
  thm "dvd_diff_commute"
  thus "(m > 1) \<and> m dvd (y - x)"
    using assms
    by simp
qed


lemma tranzitivna:
  assumes "m > 1"
  assumes "kongruentni_po_modulu x y m"
  assumes "kongruentni_po_modulu y z m"
  shows "kongruentni_po_modulu x z m"
unfolding kongruentni_po_modulu_def
proof-
  have *: "m dvd (x - y)"
    using assms
    unfolding kongruentni_po_modulu_def
    by simp
  have **: "m dvd (y - z)"
    using assms
    unfolding kongruentni_po_modulu_def
    by simp
  have "m dvd (x - y + y - z)"
    using * **
    by (smt zdvd_zdiffD)
    thm "zdvd_zdiffD"
    hence "m dvd (x - z)"
      by simp
    thus "(m > 1) \<and> (m dvd (x - z))"
      using assms
      by simp
qed


(* Za naredna tvrdjenja potreban je i nzd. *)

fun nzd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
   "nzd a b = (if b = 0 then a else nzd b (a mod b))"

value "nzd 120 28"

(* Tvrdjenje 4: Ako je a*b \<equiv> a*c (mod m)  i  nzd(a,m) = 1 
   onda je b \<equiv> c (mod m) *)

lemma pomocna_2:
  assumes "nzd a b = d"
  shows "a*x + b*y = d"
  sorry   (* dokazuje se pomocu Euklidovog algoritma *)

lemma pomocna_1:
  assumes "a dvd (b*c)"
  assumes "nzd a b = 1"
  shows "a dvd c"
proof-
  have "a*x + b*y = 1"
    using pomocna_2 `nzd a b = 1`
    by simp
  hence *:" a*c*x + b*c*y = c"
    by (metis add.right_neutral crossproduct_noteq linordered_field_class.sign_simps(6) mult.comm_neutral mult_zero_left nzd.simps(1) pomocna_2 rel_simps(76) semiring_normalization_rules(7))
  have "a dvd a*c*x"
    by simp
  hence "a dvd (a*c*x + b*c*y)"
    using assms(1)
    by simp
  thus "a dvd c"
    using *
    by simp
qed


lemma tvrdjenje_4:
  assumes "m > 1"
  assumes "kongruentni_po_modulu (a*b) (a*c) m"
  assumes "nzd a m = 1"
  shows "kongruentni_po_modulu b c m"
unfolding kongruentni_po_modulu_def
proof-
  have "m dvd (a*b - a*c)"
    using assms
    unfolding kongruentni_po_modulu_def
    by simp
  hence "m dvd (a*(b - c))"
    by (simp add: algebra_simps)
  hence "m dvd (b - c)"
    using pomocna_1 `nzd a m = 1`
    by simp
  thus "(m > 1) \<and> (m dvd (b - c))"
    using assms
    by simp
qed

(* 
  Tvrdjenje 5: Neka za prirodne brojeve m i n vece od 1 i ceo broj a vazi:
  m|a i n|a. Ako su brojevi m i n uzajamno prosti, onda m*n|a. 
*)

lemma tvrdjenje_5:
  fixes m :: nat
  fixes n :: nat 
  fixes a :: int
  assumes "m > 1"
  assumes "n > 1"
  assumes "m dvd a"
  assumes "n dvd a"
  assumes "nzd m n = 1"
  shows "m*n dvd a"
proof-
  have *:" a = m * a1"
    using assms(3)
    by (metis (mono_tags, lifting) One_nat_def add_diff_cancel_left' diff_is_0_eq dvd_div_mult_self dvd_minus_self dvd_refl less_numeral_extra(4) less_one linorder_not_le mult.right_neutral nat_diff_split nonzero_mult_div_cancel_left nzd.simps(1) of_nat_0 of_nat_1 pomocna_2 semiring_1_class.of_nat_simps(2) zero_less_diff)
  hence "n dvd m*a1"
    using assms(4) of_nat_dvd_iff 
    by blast
  hence "n dvd a1"
    using pomocna_1 assms(5)
    by simp
  hence **: "a1 = n * a2"
    by (metis (mono_tags, lifting) One_nat_def add_diff_cancel_left' diff_is_0_eq dvd_div_mult_self dvd_minus_self dvd_refl less_numeral_extra(4) less_one linorder_not_le mult.right_neutral nat_diff_split nonzero_mult_div_cancel_left nzd.simps(1) of_nat_0 of_nat_1 pomocna_2 semiring_1_class.of_nat_simps(2) zero_less_diff)
  hence "a = m*n*a2"
    using * **
    by simp
  thus "m*n dvd a"
    by simp
qed

lemma 
  assumes "m > 1"
  assumes "n > 1"
  assumes "nzd m n = 1"
  assumes "kongruentni_po_modulu a a1 m"
  assumes "kongruentni_po_modulu a a1 n"
  shows "kongruentni_po_modulu a a1 (m*n)"
proof-
  have *: "m dvd (a - a1)"
    using assms(4)
    unfolding kongruentni_po_modulu_def
    by simp
  have **: "n dvd (a - a1)"
    using assms(5)
    unfolding kongruentni_po_modulu_def
    by simp
  have "(m*n) dvd (a - a1)"
    using * ** tvrdjenje_5 assms
    by simp
  thus "kongruentni_po_modulu a a1 (m*n)" 
    using assms
    unfolding kongruentni_po_modulu_def
    using less_1_mult by blast
qed



(* Provera da li postoji resenje jednacine a*x \<equiv> b (mod m) *)
definition postoji_resenje :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"postoji_resenje a b m  = ((nzd a m) dvd b)"

value "postoji_resenje 4 9 14"
value "postoji_resenje 7 1 9"
value "postoji_resenje 8 12 28"

definition postoji_resenje2 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"postoji_resenje2 a b m  = (\<exists>x. m dvd (a*x - b))"

definition postoji_resenje3 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"postoji_resenje3 a b m  = (\<exists>x y. a*x - b = m*(-y))"

(* Provera da li je x resenje jednacine a*x \<equiv> b (mod m) *)
definition jeste_resenje :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"jeste_resenje x a b m = (m dvd (a*x - b))"

definition jeste_resenje2 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"jeste_resenje2 x a b m = (\<exists>y. a*x - b = m*(-y))"


(* Neka je d=nzd(a,m) > 1. 
   x je resenje jednacine a*x \<equiv> b (mod m) akko je resenje jednacine a*x \<equiv> b (mod m),
   gde su a'=a/d, b'=b/d i m'=m/d. *)
lemma
  assumes "d = nzd a m"
  assumes "d > 1"
  assumes "a' = a/d" "b' = b/d" "m' = m/d"
  shows "jeste_resenje2 x a b m \<longleftrightarrow> jeste_resenje2 x a' b' m'"
proof
  show "jeste_resenje2 x a b m \<Longrightarrow> jeste_resenje2 x a' b' m'"
  proof-
    assume "jeste_resenje2 x a b m"
    have "\<exists>y. a*x - b = m*(-y)"
      using assms
      unfolding jeste_resenje2_def
      using \<open>jeste_resenje2 x a b m\<close> jeste_resenje2_def by blast
    hence "\<exists>y. a*x + m*y = b"
      by (metis crossproduct_eq pomocna_2)
    hence "\<exists>y. (a/d)*x + (m/d)*y = b/d"
      by (metis (mono_tags, hide_lams) assms(4) crossproduct_eq of_nat_add of_nat_mult pomocna_2)
    hence "\<exists>y. a'*x + m'*y = b'"
      using assms
      by (metis add.commute add_diff_cancel_left' add_diff_cancel_right add_diff_cancel_right' add_mult_distrib add_mult_distrib2 crossproduct_eq diff_commute left_add_mult_distrib less_diff_conv mult.commute not_add_less1 pomocna_2 right_diff_distrib' semiring_normalization_rules(2) semiring_normalization_rules(3))
    thus "jeste_resenje2 x a b m \<Longrightarrow> jeste_resenje2 x a' b' m'"
      unfolding jeste_resenje2_def
      by auto
  qed
next
  show "jeste_resenje2 x a' b' m' \<Longrightarrow> jeste_resenje2 x a b m"
  proof-
    assume "jeste_resenje2 x a' b' m'"
    have "\<exists>y. a'*x - b' = m'*(-y)"
      using assms
      unfolding jeste_resenje2_def
      using \<open>jeste_resenje2 x a' b' m'\<close> jeste_resenje2_def by blast
    hence "\<exists>y. a'*x + m'*y = b'"
      by (metis crossproduct_eq pomocna_2)
    hence "\<exists>y. a'*d*x + m'*d*y = b'*d"
      by (metis (mono_tags, hide_lams) assms(4) crossproduct_eq of_nat_add of_nat_mult pomocna_2)
    hence "\<exists>y. a*x + m*y = b"
      using assms
       by (metis add.commute add_diff_cancel_left' add_diff_cancel_right add_diff_cancel_right' add_mult_distrib add_mult_distrib2 crossproduct_eq diff_commute left_add_mult_distrib less_diff_conv mult.commute not_add_less1 pomocna_2 right_diff_distrib' semiring_normalization_rules(2) semiring_normalization_rules(3))
    thus "jeste_resenje2 x a' b' m' \<Longrightarrow> jeste_resenje2 x a b m"
      unfolding jeste_resenje2_def
      by auto
  qed
qed


definition prost_broj :: "nat \<Rightarrow> bool" where 
"prost_broj p = (p > 1 \<and> (\<forall>m. m dvd p \<longrightarrow> m = 1 \<or> m = p))"


definition lista_brojeva_Ojlerove_fje :: "nat \<Rightarrow> nat list" where
  "lista_brojeva_Ojlerove_fje n = filter (\<lambda>m . nzd m n = 1) [1..<n]"

definition Ojlerova_fja :: "nat \<Rightarrow> nat" where
  "Ojlerova_fja n = length(filter (\<lambda>m . nzd m n = 1) [1..<n])"

value "lista_brojeva_Ojlerove_fje 10"
value "Ojlerova_fja 10"

lemma ojl_lema1:
  assumes "k \<ge> 1"
  assumes "prost_broj p"
  shows "Ojlerova_fja (p^k) = p^k - p^(k-1)"
proof (induction k)
case 0
  then show ?case
  unfolding Ojlerova_fja_def prost_broj_def
    by simp
next
  case (Suc k)
  then show ?case
    by (metis Groups.mult_ac(2)  nzd.simps one_neq_zero pomocna_2 times_nat.simps(1))
qed


lemma ojl_lema2:
  assumes "k \<ge> 1"
  assumes "prost_broj p"
  shows "Ojlerova_fja (p^k) = p^k *(1 - 1/p)"
proof-
  have 1: "Ojlerova_fja (p^k) =  p^k - p^(k-1)"
    using ojl_lema1 assms
    by simp
  also have 2: "... = p^k - (p^k * 1/p)"
    by (smt One_nat_def Suc_leI assms(1) diff_divide_distrib diff_is_0_eq' diff_le_self le_numeral_extra(4) mult.right_neutral nat_zero_less_power_iff neq0_conv nonzero_mult_div_cancel_left of_nat_diff of_nat_eq_iff of_nat_mult power_eq_if power_increasing)
      (*by (smt One_nat_def Suc_leI assms(1) diff_is_0_eq divide_self_if eq_iff mult.assoc mult.right_neutral mult_less_cancel2 nat_zero_less_power_iff nonzero_mult_div_cancel_left not_le of_nat_diff of_nat_mono of_nat_mult power_commutes power_eq_if zero_le_one zero_less_one)
  *)
    also have 3: "... = p^k * 1 - (p^k * 1/p)"
      by simp
    also have 4: "... = p^k * (1 - 1/p)"
      by (simp add: right_diff_distrib')
    thus ?thesis
      using 1 2 3 4
      by simp
qed


lemma ojl_proizvod_dva:
  assumes "m > 1" "n > 1"
  assumes "nzd m n = 1"
  shows "Ojlerova_fja (m*n) = (Ojlerova_fja m) * (Ojlerova_fja n)"
  unfolding Ojlerova_fja_def
  by (metis crossproduct_noteq length_filter_conv_card pomocna_2)

value "fold ( * ) [1,2,3,4::nat] 1"
value "[1..<5]"

lemma ojl_proizvod_uopstenje:
  fixes n1::nat
  fixes nk::nat
  (*assumes "n1 > 1" "nk > 1"*)
  (*assumes "nzd n1 nk = 1"*)
  assumes "length [n1..<nk] = k"
  assumes "\<forall>x y. x\<in>set[n1..<nk] \<and> y\<in>set[n1..<nk] \<and> (nzd x y = 1) \<and> x>1 \<and> y>1"
  shows "Ojlerova_fja (fold ( * ) [n1..<nk] 1) = fold ( * ) [Ojlerova_fja(n1)..<Ojlerova_fja(nk)] 1"
  using assms ojl_proizvod_dva
  by blast

fun proizvod_prostih :: "nat list \<Rightarrow> nat list \<Rightarrow> nat" where
   "proizvod_prostih [] _ = 1"
|  "proizvod_prostih _ [] = 1"
|  "proizvod_prostih (p # ps) (a # as) = p^a * (proizvod_prostih ps as)"

primrec proizvod_1_minus_1krozP :: "nat list \<Rightarrow> real" where
   "proizvod_1_minus_1krozP [] = 1"
|  "proizvod_1_minus_1krozP (p # ps) = (1 - 1/p) * (proizvod_1_minus_1krozP ps)"

lemma 
  fixes P::"nat list"
  fixes A::"nat list"
  assumes "length P = k" "length A = k"
  assumes "\<forall>p\<in>(set P) . prost_broj p"
  assumes "n = proizvod_prostih P A"
  shows "Ojlerova_fja n = n * (proizvod_1_minus_1krozP P)"
  using assms
  by (metis One_nat_def diff_is_0_eq' le_numeral_extra(4) mult.right_neutral mult_0_right nat_diff_split of_nat_1 order_less_irrefl pomocna_2 semiring_1_class.of_nat_simps(2) zero_less_diff zero_less_one)




end