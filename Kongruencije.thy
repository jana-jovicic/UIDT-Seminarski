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

lemma tvrdjenje_6:
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

(* a \<equiv>m b and c \<equiv>m d \<Longrightarrow> a−c \<equiv>m b−d *)
lemma tvrdjenje_7:
  assumes "m > 1"
  assumes "kongruentni_po_modulu a b m"
  assumes "kongruentni_po_modulu c d m"
  shows "kongruentni_po_modulu (a - c) (b - d) m"
proof-
  have *: "m dvd (a - b)"
    using assms(2) kongruentni_po_modulu_def
    by auto
  have **: "m dvd (c - d)"
    using assms(3) kongruentni_po_modulu_def
    by auto
  have "m dvd ((a - b) - (c - d))"
    using * **
    by auto
  hence "m dvd ((a - c) - (b - d))"
    by (simp add: algebra_simps)
  hence "(m > 1) \<and> (m dvd (a - c) - (b - d))"
      using assms(1)
      by simp
  thus ?thesis
    unfolding kongruentni_po_modulu_def
    by simp
qed

(* a \<equiv>m 0 iff m|a;  *)
lemma tvrdjenje_8:
  assumes "m > 1"
  shows "kongruentni_po_modulu a 0 m \<longleftrightarrow> m dvd a"
proof
  show "kongruentni_po_modulu a 0 m \<Longrightarrow> int m dvd a"
  proof-
    assume "kongruentni_po_modulu a 0 m"
    hence "m dvd (a - 0)"
      unfolding kongruentni_po_modulu_def
      by simp
    thus "m dvd a"
      by simp
  qed
next
  show "m dvd a \<Longrightarrow> kongruentni_po_modulu a 0 m"
  proof-
    assume "m dvd a"
    hence "m dvd (a - 0)"
      by simp
    thus "kongruentni_po_modulu a 0 m"
      unfolding kongruentni_po_modulu_def
      using assms
      by simp
  qed
qed

(* If a \<equiv> b mod m, and c > 1, then ca \<equiv> cb mod cm *)
lemma tvrdjenje_9:
  assumes "c > 1"
  assumes "m > 1"
  assumes "kongruentni_po_modulu a b m"
  shows "kongruentni_po_modulu (c*a) (c*b) (c*m)"
proof-
  have *: "c*m > 1"
    using assms(1) assms(2) less_1_mult 
    by blast
  have "m dvd (a - b)"
    using assms kongruentni_po_modulu_def
    by auto
  hence "c*m dvd c*(a - b)"
    by simp
  hence "c*m dvd (c*a - c*b)"
    by (simp add: algebra_simps)
  thus ?thesis
    unfolding kongruentni_po_modulu_def
    using assms *
    by simp
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

lemma jeste_resenje_sledi_postoji_resenje:
"jeste_resenje x a b m \<longrightarrow> postoji_resenje2 a b m"
  using jeste_resenje_def postoji_resenje2_def
  by blast

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


definition nzs_dva_broja :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"nzs_dva_broja a b = a*b div (nzd a b)"

primrec nzs_liste_brojeva :: "nat list \<Rightarrow> nat" where
  "nzs_liste_brojeva [] = 1"
| "nzs_liste_brojeva (x # xs) = nzs_dva_broja x (nzs_liste_brojeva xs)"

value "nzs_dva_broja 6 8"
value "nzs_liste_brojeva [3, 4, 12]"

definition postoji_resenje_sistema :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where
  "postoji_resenje_sistema as ms = (\<forall> i j . i\<in>set([0..<(length as)]) \<and> j\<in>set([0..(length ms)]) \<and> (i = j) \<and> (postoji_resenje 1 (as ! i) (ms ! j)))"

definition jeste_resenje_sistema :: "nat \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool" where
"jeste_resenje_sistema x as ms = (\<forall> i j . i\<in>set([0..<(length as)]) \<and> j\<in>set([0..(length ms)]) \<and> (i = j) \<and> (jeste_resenje x 1 (as ! i) (ms ! j)))"

lemma jeste_resenje_sledi_postoji_resenje_sistema:
"jeste_resenje_sistema x as ms \<longrightarrow> postoji_resenje_sistema as ms"
  using jeste_resenje_sistema_def 
  by blast

primrec lista_nzd :: "nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "lista_nzd [] y = []"
| "lista_nzd (x # xs) y = (nzd x y) # (lista_nzd xs y)"

fun lista_istih_elemenata' :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "lista_istih_elemenata' x 0 xs = xs"
| "lista_istih_elemenata' x len xs = [x] @ (lista_istih_elemenata' x (len-1) xs)"

fun lista_istih_elemenata :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
"lista_istih_elemenata x len = lista_istih_elemenata' x len []"

value "lista_istih_elemenata 2 10"

lemma pomocna1_za_kinesku_teoremu: 
  "nzd (nzs_liste_brojeva xs) y = nzs_liste_brojeva (lista_nzd xs y)"
  sorry

lemma pomocna2_za_kinesku_teoremu: 
  "(nzs_liste_brojeva (lista_nzd xs y)) dvd z = (\<forall>x\<in>set(xs) . (nzd x y) dvd z)"
  sorry

lemma pomocna3_za_kinesku_teoremu:
  fixes x y z :: "nat"
  shows "x - y = (x - z) + (z - y)"
  sorry

lemma pomocna4_za_kinesku_teoremu:
"(postoji_resenje_sistema as ms \<and> postoji_resenje x a m) \<longrightarrow> postoji_resenje_sistema (a # as) (m # ms)"
  using postoji_resenje_sistema_def by blast

lemma pomocna5_za_kinesku_teoremu: "a dvd c \<longrightarrow> nzd a b dvd c"
  by (metis diff_is_0_eq' le_add_diff_inverse2 pomocna3_za_kinesku_teoremu rel_simps(47) zero_le_one zero_neq_one)

lemma pomocna6_za_kinesku_teoremu: "a dvd b \<and> a dvd c \<longrightarrow> a  dvd (b+c)"
  using le_add_diff_inverse2 pomocna3_za_kinesku_teoremu by presburger

lemma kineska_teorema_o_ostacima:
  fixes x::nat
  fixes as ms :: "nat list"
  assumes "length as = length ms"
  shows "((\<forall>i j . (k = length as) \<and> (k = length ms) \<and> i\<in>set([0..<k]) \<and> j\<in>set([0..<k]) \<and> i\<noteq>j \<and> ((nzd (ms ! i) (ms ! j)) dvd ((as ! i) - (as ! j))) \<and> jeste_resenje_sistema x as ms ) \<longrightarrow> 
        ((postoji_resenje_sistema as ms) \<and> (\<exists>t . jeste_resenje_sistema (x + (nzs_liste_brojeva ms)*t) as ms)))"
proof(induction k)
case 0
  then show ?case
    using assms jeste_resenje_sistema_def
    by blast
next
  case (Suc k)
  then show ?case
  proof-

    have prvi_deo: "(\<forall>i j. Suc k = length as \<and> Suc k = length ms \<and>
          i \<in> set [0..<Suc k] \<and> j \<in> set [0..<Suc k] \<and> i \<noteq> j \<and> 
          nzd (ms ! i) (ms ! j) dvd as ! i - as ! j) \<and> (jeste_resenje_sistema x (take k as) (take k ms))
           \<Longrightarrow> postoji_resenje_sistema as ms"
    proof-
      assume leva_strana_implikacije: "(\<forall>i j. Suc k = length as \<and> Suc k = length ms \<and>
          i \<in> set [0..<Suc k] \<and> j \<in> set [0..<Suc k] \<and> i \<noteq> j \<and> 
          nzd (ms ! i) (ms ! j) dvd (as ! i - as ! j)) \<and> jeste_resenje_sistema x (take k as) (take k ms)"

      have 1: "jeste_resenje_sistema x (take k as) (take k ms)"
        using leva_strana_implikacije
        by blast

      (* Na osnovu induktivne hipoteze znamo da postoji resenje sistema od k jednacina: *)
      have postoji_res_sistema_duzine_k: "postoji_resenje_sistema (take k as) (take k ms)"
        using 1 jeste_resenje_sledi_postoji_resenje_sistema Suc
        by blast

      (* Dokaz da postoji resenje jednacine x \<equiv> a_k+1 (mod m_k+1) *)
      have postoji_res_poslednje_jednacine: "postoji_resenje ((nzs_liste_brojeva (take k ms))) ((as ! Suc k)-x) (ms ! Suc k)"
      proof-
        (* nzd(m_i, m_k+1) | (a_k+1 - a_i): *)
        have deli_aSuc_minus_ai: "\<forall>i . i\<in>set[0..<k] \<and> ((nzd (ms ! i) (ms ! Suc k)) dvd ((as ! Suc k) - (as ! i)))"
          by (metis add.right_neutral diff_add_zero linordered_semidom_class.add_diff_inverse not_one_less_zero pomocna3_za_kinesku_teoremu zero_neq_one)

        (* Dokaz da nzd(m_i, m_k+1) | (a_i - x): *)
        have *:"jeste_resenje_sistema x (take k as) (take k ms)"
          using "1" jeste_resenje_sistema_def
          by blast
        have **:"jeste_resenje_sistema x (take k as) (take k ms) \<longrightarrow> ( \<forall>i . i\<in>set[0..<k] \<and> ((ms ! i) dvd ((as ! i) - x)))"
          using jeste_resenje_sistema_def
          by blast
        have "\<forall>i . i\<in>set[0..<k] \<and> ((ms ! i) dvd ((as ! i) - x))"
          using * **
          by blast
        hence deli_ai_minus_x: "\<forall>i . i\<in>set[0..<k] \<and> ((nzd (ms ! i) (ms ! Suc k))dvd ((as ! i) - x))"
          using pomocna5_za_kinesku_teoremu 
          by blast

        (* a_k+1 - x moze da se napise kao (a_k+1 - a_i) + (a_i - x) *)
        have #: "\<forall>i\<in>set[0..<k].  (as ! Suc k) - x = ((as ! Suc k) - (as ! i)) + ((as ! i) - x)"
          using pomocna3_za_kinesku_teoremu
          by blast

        (* posto nzd deli svaki od sabiraka, onda deli i ceo zbir: *)
        have ##: "\<forall>i\<in>set[0..<k] . ((nzd (ms ! i) (ms ! Suc k)) dvd (((as ! Suc k) - (as ! i)) + ((as ! i) - x)))"
          using pomocna6_za_kinesku_teoremu deli_ai_minus_x deli_aSuc_minus_ai
          by blast
        (* odnosno, deli i a_k+1 - x *)
        have "\<forall>i\<in>set[0..<k] . ((nzd (ms ! i) (ms ! Suc k)) dvd ((as ! Suc k) - x))"
          using # ## "*" jeste_resenje_sistema_def 
          by blast

        (* \<forall>i nzd(m_i, m_k+1) | (a_k+1 - x) \<Longrightarrow> nzs(nzd(m_1, m_k+1), ..., nzd(m_k, m_k+1)) | (a_k+1 - x) *)
        hence "nzs_liste_brojeva (lista_nzd (take k ms) (ms ! Suc k)) dvd ((as ! Suc k) - x)"
          using pomocna2_za_kinesku_teoremu  "*" jeste_resenje_sistema_def
          by blast
        (* \<Longrightarrow> nzd(nzs(m1,...,mk), m_k+1) | (a_k+1 - x) *)
        hence "(nzd (nzs_liste_brojeva (take k ms)) (ms ! Suc k)) dvd ((as ! Suc k) - x)"
          using 1 pomocna1_za_kinesku_teoremu
          by simp
        (* \<Longrightarrow> postoji resenje jednacine nzs(m1,...,mk)*y \<equiv> (a_k+1 - x) mod m_k+1 *)
        thus "postoji_resenje ((nzs_liste_brojeva (take k ms))) (as ! Suc k - x) (ms ! Suc k)"
          unfolding postoji_resenje_def
          using "*" jeste_resenje_sistema_def by blast

      qed

      (* Posto postoji resenje sistema od k jednacina i postoji resenje te poslednje jednacine,
         onda postoji i resenje celog sistema od k+1 jednacina. *)
      have *:"postoji_resenje_sistema as ms"
        using postoji_res_sistema_duzine_k postoji_res_poslednje_jednacine pomocna4_za_kinesku_teoremu
        using "1" jeste_resenje_sistema_def 
        by blast
      thus ?thesis
        using *
        by blast
    qed

    have drugi_deo: "(jeste_resenje_sistema x as ms \<Longrightarrow> (\<exists>t. jeste_resenje_sistema (x + nzs_liste_brojeva ms * t) as ms))"
    proof-
      fix x1::nat
      (* x je resenje sistema - iz leve strane implikacije: \<forall>i x \<equiv> ai (mod mi) *)
      assume "jeste_resenje_sistema x as ms"  
      (* x1 je proizvoljno resenje sistema: \<forall>i x1 \<equiv> ai (mod mi)  *)
      assume "jeste_resenje_sistema x1 as ms" 
      (* Iz te dve pretpostavke onda vazi: \<forall>i x1 \<equiv> x (mod mi) *)
      have *: "jeste_resenje_sistema x1 (lista_istih_elemenata x (length ms)) ms"
        using `jeste_resenje_sistema x1 as ms` `jeste_resenje_sistema x as ms` 
        using Zero_not_Suc add_diff_cancel_right' diff_add_zero plus_1_eq_Suc pomocna3_za_kinesku_teoremu
        by presburger
      (* Odatle sledi da \<forall>i  mi | x1-x *)
      hence "\<forall>i\<in>set[0..<length ms] . (ms!i) dvd (x1 - x)"
        using jeste_resenje_sistema_def
        by blast
      (* Odnosno da nzs(m1,...,mk) | x1-x *)
      hence "(nzs_liste_brojeva ms) dvd (x1 - x)"
        by (metis diff_add_inverse  gcd_nat.order_iff_strict minus_nat.diff_0 pomocna3_za_kinesku_teoremu zero_diff)
     
     (* Odatle sledi da x1-x moze da se zapise kao nzs(m1,...,mk)*t za neko t *)
      hence 1: "\<exists>t . (x1 - x) = (nzs_liste_brojeva ms)*t"
        by blast
      (* Znamo da \<forall>i\<in>{1,..,k} vazi nzs(m1,...,mk) \<equiv> 0 (mod mi) tj. da je nzs koji sadrzi mi deljiv sa mi *)
      have 2: "jeste_resenje_sistema (nzs_liste_brojeva ms) (lista_istih_elemenata 0 (length ms)) ms"
        using * jeste_resenje_sistema_def 
        by blast

      (* iz 1 i 2 sledi da je svaki broj oblika x + nzs(m1,...,mk)*t resenje sistema *)
      have "\<exists>t. jeste_resenje_sistema (x + nzs_liste_brojeva ms * t) as ms"
        using 1 2  Suc.IH `jeste_resenje_sistema x as ms`
        by (metis mult_0_right semiring_normalization_rules(6))
      thus ?thesis
        by blast
    qed

    thus ?thesis
      using prvi_deo drugi_deo
      by blast

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
  by (metis crossproduct_noteq  pomocna_2)

value "Ojlerova_fja (fold ( * ) [3,7] 1)"
value "fold (\<lambda>x acc . acc * Ojlerova_fja x) [3,7] 1"
value "Ojlerova_fja 3"
value "Ojlerova_fja 7"

lemma ojl_proizvod_uopstenje:
  fixes ns::"nat list"
  assumes "\<forall>n1 n2 . n1\<in>set(ns) \<and> n2\<in>set(ns) \<and> n1 \<noteq> n2 \<and> nzd n1 n2 = 1"
  shows "Ojlerova_fja (fold ( * ) ns 1) = fold (\<lambda>n acc . acc * Ojlerova_fja n) ns 1"
  using assms by blast 

fun proizvod_prostih :: "nat list \<Rightarrow> nat list \<Rightarrow> nat" where
"proizvod_prostih ps as = fold (\<lambda> par acc . (fst par)^(snd par) * acc ) (zip ps as) 1"

value "proizvod_prostih [1,2,3] [2,2,2]"

primrec proizvod_1_minus_1krozP :: "nat list \<Rightarrow> real" where
   "proizvod_1_minus_1krozP [] = 1"
|  "proizvod_1_minus_1krozP (p # ps) = (1 - 1/p) * (proizvod_1_minus_1krozP ps)"

lemma 
  fixes ps::"nat list"
  fixes as::"nat list"
  assumes "length ps = k" "length as = k"
  assumes "\<forall>p\<in>(set ps) . prost_broj p"
  assumes "n = proizvod_prostih ps as"
  assumes "\<forall>a\<in>(set as) . a \<ge> 1"
  shows "Ojlerova_fja n = n * (proizvod_1_minus_1krozP ps)"
  (*using assms
  by (metis One_nat_def diff_is_0_eq' le_numeral_extra(4) mult.right_neutral mult_0_right nat_diff_split of_nat_1 order_less_irrefl pomocna_2 semiring_1_class.of_nat_simps(2) zero_less_diff zero_less_one)
  *)
proof-
  have "Ojlerova_fja n = Ojlerova_fja (proizvod_prostih ps as)"
    using assms(4)
    by auto
  (* f(n) = f(p1^a1 * ...* pk^ak) *)
  also have "... = Ojlerova_fja (fold (\<lambda> par acc . (fst par)^(snd par) * acc ) (zip ps as) 1)"
    using proizvod_prostih.simps
    by simp
       (* = f(p1^a1)* ... * f(pk^ak) *)
  also have "... = fold (\<lambda>par acc . acc * Ojlerova_fja ((fst par)^(snd par))) (zip ps as) 1"
    using ojl_proizvod_uopstenje
    by (metis calculation crossproduct_noteq mult.commute mult.left_neutral  pomocna_2 zero_neq_one)
       (* = p1^a1 * (1 - 1/p1) * ... * pk^ak * (1 - 1/pk) *)  
  also have "... = fold (\<lambda>par acc . acc * (fst par)^(snd par) * (1 - 1/(fst par))) (zip ps as) 1"
    using ojl_lema2
    by (metis (mono_tags, lifting) crossproduct_noteq one_neq_zero pomocna_2)
       (* = p1^a1 * ... * pk^ak * (1 - 1/p1) * ... * (1 - 1/pk) *)
  also have "... = (fold (\<lambda>par acc . (fst par)^(snd par) * acc ) (zip ps as) 1) * (fold (\<lambda>p acc . acc * (1 - 1/p)) ps 1)"
    by (metis crossproduct_noteq one_neq_zero pomocna_2)
  also have "... = (proizvod_prostih ps as) * (fold (\<lambda>p acc . acc * (1 - 1/p)) ps 1)"
    using proizvod_prostih.simps
    by auto
  thus ?thesis
    by (metis (mono_tags, lifting) crossproduct_noteq one_neq_zero pomocna_2)
qed

definition redukovan_sistem :: "nat set \<Rightarrow> nat \<Rightarrow> bool" where
"redukovan_sistem rs n = (\<forall>z . \<exists>!r\<in>rs . (n > 1) \<and> (nzd z n = 1) \<and> (kongruentni_po_modulu z r n))"

lemma Ojlerova_teorema:
  fixes a n :: nat
  assumes "a > 1" "n > 1"
  assumes "nzd a n = 1"
  shows "kongruentni_po_modulu (a^(Ojlerova_fja n)) 1 n"
  using assms
  by (metis (no_types, hide_lams) crossproduct_noteq kongruentni_po_modulu_def of_nat_0_eq_iff of_nat_0_less_iff one_neq_zero pomocna_2)

lemma Mala_Fermaova_teorema:
  fixes p a :: nat
  assumes "a > 1" "p > 1"
  assumes "prost_broj p"
  assumes "\<not>(p dvd a)"
  shows "kongruentni_po_modulu (a^(p-1)) 1 p"
proof-
  have "Ojlerova_fja p = p^1 - p^(1-1)"
    using assms(3) ojl_lema1[of "1" "p"]
    by simp
  hence *: "Ojlerova_fja p = p - 1"
    by simp

  have "nzd a p = 1"
    using assms
    by (metis One_nat_def crossproduct_noteq nat_mult_1_right nzd.simps plus_1_eq_Suc pomocna_2 zero_neq_one)
  hence "kongruentni_po_modulu (a^(Ojlerova_fja p)) 1 p"
    using assms Ojlerova_teorema
    by auto
  thus ?thesis
    using *
    by simp
qed


end