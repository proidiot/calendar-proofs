theory Month
imports Main
begin

type_synonym Year = int
type_synonym Day = int
 
datatype Month =
	January | February | March | April | May | June |
	July | August | September | October | November | December
 
fun next_month :: "Year \<times> Month \<Rightarrow> Year \<times> Month" where
	"next_month (y,January) = (y,February)" |
	"next_month (y,February) = (y,March)" |
	"next_month (y,March) = (y,April)" |
	"next_month (y,April) = (y,May)" |
	"next_month (y,May) = (y,June)" |
	"next_month (y,June) = (y,July)" |
	"next_month (y,July) = (y,August)" |
	"next_month (y,August) = (y,September)" |
	"next_month (y,September) = (y,October)" |
	"next_month (y,October) = (y,November)" |
	"next_month (y,November) = (y,December)" |
	"next_month (y,December) = (y+1,January)"

theorem next_month_month_change:
		"(y',m') = next_month (y,m)
		\<Longrightarrow> m' \<noteq> m"
	using
		Month.exhaust
		next_month.simps
	by (smt (z3) Pair_inject)

theorem next_month_year_change:
		"(y',m') = next_month (y,m)
		\<Longrightarrow> y' = y \<and> m \<noteq> December \<and> m' \<noteq> January
        \<or> y' = y + 1 \<and> m = December \<and> m' = January"
proof -
  assume "(y',m') = next_month (y,m)"
  have "y' = y \<or> y' \<noteq> y" by simp
  thus "y' = y \<and> m \<noteq> December \<and> m' \<noteq> January
        \<or> y' = y + 1 \<and> m = December \<and> m' = January"
  proof (elim disjE)
    assume "y' = y"
    hence "y' = y \<and> m \<noteq> December \<and> m' \<noteq> January"
      using
        `(y',m') = next_month (y,m)`
        Month.exhaust
        next_month.simps
      by (smt (z3) Pair_inject)
    thus ?thesis by blast
  next
    assume "y' \<noteq> y"
    hence "y' = y + 1 \<and> m = December \<and> m' = January"
      using
        `(y',m') = next_month (y,m)`
        Month.exhaust
        next_month.simps
      by (smt (verit, ccfv_SIG) Pair_inject)
    thus ?thesis by blast
  qed
qed

theorem next_month_well_defined:
		"(y1,m1) = next_month (y,m) \<and> (y2,m2) = next_month (y,m)
		\<Longrightarrow> (y1,m1) = (y2,m2)"
	by simp

theorem next_month_injective:
		"(y,m) = next_month (y1,m1) \<and> (y,m) = next_month (y2,m2)
		\<Longrightarrow> (y1,m1) = (y2,m2)"
proof -
	assume "(y,m) = next_month (y1,m1) \<and> (y,m) = next_month (y2,m2)"
	hence "(y,m) = next_month (y1,m1)" "(y,m) = next_month (y2,m2)" by simp+
	thus "(y1,m1) = (y2,m2)"
	proof (cases m1)
	  case assm: January
	  hence "y = y1" using `(y,m) = next_month (y1,m1)` next_month_year_change by blast
	  have "m = February" using assm `(y,m) = next_month (y1,m1)` by fastforce
	  have "m2 = January"
	    using
        `m = February`
	      `(y,m) = next_month (y2,m2)`
        Month.exhaust
        Month.simps
        next_month.simps
        next_month_year_change
	    by (smt (z3))
	  hence "y = y2" using `(y,m) = next_month (y2,m2)` next_month_year_change by blast
	  thus "(y1,m1) = (y2,m2)"
	    using
	      assm
        `y = y1`
        `m2 = January`
      by simp
	next
	  case assm: February
	  hence "y = y1" using `(y,m) = next_month (y1,m1)` next_month_year_change by blast
	  have "m = March" using assm `(y,m) = next_month (y1,m1)` by fastforce
	  have "m2 = February"
	    using
        `m = March`
	      `(y,m) = next_month (y2,m2)`
        Month.exhaust
        Month.simps
        next_month.simps
        next_month_year_change
	    by (smt (z3))
	  hence "y = y2" using `(y,m) = next_month (y2,m2)` next_month_year_change by blast
	  thus "(y1,m1) = (y2,m2)"
	    using
	      assm
        `y = y1`
        `m2 = February`
      by simp
	next
	  case assm: March
	  hence "y = y1" using `(y,m) = next_month (y1,m1)` next_month_year_change by blast
	  have "m = April" using assm `(y,m) = next_month (y1,m1)` by fastforce
	  have "m2 = March"
	    using
        `m = April`
	      `(y,m) = next_month (y2,m2)`
        Month.exhaust
        Month.simps
        next_month.simps
        next_month_year_change
	    by (smt (z3))
	  hence "y = y2" using `(y,m) = next_month (y2,m2)` next_month_year_change by blast
	  thus "(y1,m1) = (y2,m2)"
	    using
	      assm
        `y = y1`
        `m2 = March`
      by simp
	next
	  case assm: April
	  hence "y = y1" using `(y,m) = next_month (y1,m1)` next_month_year_change by blast
	  have "m = May" using assm `(y,m) = next_month (y1,m1)` by fastforce
	  have "m2 = April"
	    using
        `m = May`
	      `(y,m) = next_month (y2,m2)`
        Month.exhaust
        Month.simps
        next_month.simps
        next_month_year_change
	    by (smt (z3))
	  hence "y = y2" using `(y,m) = next_month (y2,m2)` next_month_year_change by blast
	  thus "(y1,m1) = (y2,m2)"
	    using
	      assm
        `y = y1`
        `m2 = April`
      by simp
	next
	  case assm: May
	  hence "y = y1" using `(y,m) = next_month (y1,m1)` next_month_year_change by blast
	  have "m = June" using assm `(y,m) = next_month (y1,m1)` by fastforce
	  have "m2 = May"
	    using
        `m = June`
	      `(y,m) = next_month (y2,m2)`
        Month.exhaust
        Month.simps
        next_month.simps
        next_month_year_change
	    by (smt (z3))
	  hence "y = y2" using `(y,m) = next_month (y2,m2)` next_month_year_change by blast
	  thus "(y1,m1) = (y2,m2)"
	    using
	      assm
        `y = y1`
        `m2 = May`
      by simp
	next
	  case assm: June
	  hence "y = y1" using `(y,m) = next_month (y1,m1)` next_month_year_change by blast
	  have "m = July" using assm `(y,m) = next_month (y1,m1)` by fastforce
	  have "m2 = June"
	    using
        `m = July`
	      `(y,m) = next_month (y2,m2)`
        Month.exhaust
        Month.simps
        next_month.simps
        next_month_year_change
	    by (smt (z3))
	  hence "y = y2" using `(y,m) = next_month (y2,m2)` next_month_year_change by blast
	  thus "(y1,m1) = (y2,m2)"
	    using
	      assm
        `y = y1`
        `m2 = June`
      by simp
	next
	  case assm: July
	  hence "y = y1" using `(y,m) = next_month (y1,m1)` next_month_year_change by blast
	  have "m = August" using assm `(y,m) = next_month (y1,m1)` by fastforce
	  have "m2 = July"
	    using
        `m = August`
	      `(y,m) = next_month (y2,m2)`
        Month.exhaust
        Month.simps
        next_month.simps
        next_month_year_change
	    by (smt (z3))
	  hence "y = y2" using `(y,m) = next_month (y2,m2)` next_month_year_change by blast
	  thus "(y1,m1) = (y2,m2)"
	    using
	      assm
        `y = y1`
        `m2 = July`
      by simp
	next
	  case assm: August
	  hence "y = y1" using `(y,m) = next_month (y1,m1)` next_month_year_change by blast
	  have "m = September" using assm `(y,m) = next_month (y1,m1)` by fastforce
	  have "m2 = August"
	    using
        `m = September`
	      `(y,m) = next_month (y2,m2)`
        Month.exhaust
        Month.simps
        next_month.simps
        next_month_year_change
	    by (smt (z3))
	  hence "y = y2" using `(y,m) = next_month (y2,m2)` next_month_year_change by blast
	  thus "(y1,m1) = (y2,m2)"
	    using
	      assm
        `y = y1`
        `m2 = August`
      by simp
	next
	  case assm: September
	  hence "y = y1" using `(y,m) = next_month (y1,m1)` next_month_year_change by blast
	  have "m = October" using assm `(y,m) = next_month (y1,m1)` by fastforce
	  have "m2 = September"
	    using
        `m = October`
	      `(y,m) = next_month (y2,m2)`
        Month.exhaust
        Month.simps
        next_month.simps
        next_month_year_change
	    by (smt (z3))
	  hence "y = y2" using `(y,m) = next_month (y2,m2)` next_month_year_change by blast
	  thus "(y1,m1) = (y2,m2)"
	    using
	      assm
        `y = y1`
        `m2 = September`
      by simp
	next
	  case assm: October
	  hence "y = y1" using `(y,m) = next_month (y1,m1)` next_month_year_change by blast
	  have "m = November" using assm `(y,m) = next_month (y1,m1)` by fastforce
	  have "m2 = October"
	    using
        `m = November`
	      `(y,m) = next_month (y2,m2)`
        Month.exhaust
        Month.simps
        next_month.simps
        next_month_year_change
	    by (smt (z3))
	  hence "y = y2" using `(y,m) = next_month (y2,m2)` next_month_year_change by blast
	  thus "(y1,m1) = (y2,m2)"
	    using
	      assm
        `y = y1`
        `m2 = October`
      by simp
	next
	  case assm: November
	  hence "y = y1" using `(y,m) = next_month (y1,m1)` next_month_year_change by blast
	  have "m = December" using assm `(y,m) = next_month (y1,m1)` by fastforce
	  have "m2 = November"
	    using
        `m = December`
	      `(y,m) = next_month (y2,m2)`
        Month.exhaust
        Month.simps
        next_month.simps
        next_month_year_change
	    by (smt (z3))
	  hence "y = y2" using `(y,m) = next_month (y2,m2)` next_month_year_change by blast
	  thus "(y1,m1) = (y2,m2)"
	    using
	      assm
        `y = y1`
        `m2 = November`
      by simp
	next
	  case assm: December
	  hence "y = y1+1" using `(y,m) = next_month (y1,m1)` next_month_year_change by simp
	  have "m = January" using assm `(y,m) = next_month (y1,m1)` by simp
	  have "m2 = December"
	    using
        `m = January`
	      `(y,m) = next_month (y2,m2)`
        Month.exhaust
        Month.simps
        next_month.simps
        next_month_year_change
	    by (smt (z3))
	  hence "y = y2 + 1" using `(y,m) = next_month (y2,m2)` next_month_year_change by simp
	  thus "(y1,m1) = (y2,m2)"
	    using
	      assm
        `y = y1 + 1`
        `m2 = December`
      by simp
	qed
qed

lemma next_month_antisymmetry:
    "(y',m') = next_month (y,m) \<Longrightarrow> (y,m) \<noteq> next_month (y',m')"
  using
    Month.exhaust
    next_month.simps
    next_month_year_change
  by (smt (z3))

inductive months_later :: "Year \<times> Month \<Rightarrow> Year \<times> Month \<Rightarrow> nat \<Rightarrow> bool" where
Self: "months_later (y,m) (y,m) 0" |
Later:
  "months_later (y0,m0) (y1,m1) n \<and> (y2,m2) = next_month (y1,m1)
  \<Longrightarrow> months_later (y0,m0) (y2,m2) (Suc n)"

theorem months_later_sum:
    "months_later (y0,m0) (y1,m1) n1 \<and> months_later (y1,m1) (y2,m2) n2
    \<Longrightarrow> months_later (y0,m0) (y2,m2) (n1+n2)"
proof -
  assume "months_later (y0,m0) (y1,m1) n1 \<and> months_later (y1,m1) (y2,m2) n2"
  hence
      "months_later (y0,m0) (y1,m1) n1"
      "months_later (y1,m1) (y2,m2) n2"
    by simp+
  show "months_later (y0,m0) (y2,m2) (n1+n2)"
    using `months_later (y1,m1) (y2,m2) n2`
  proof (induction "(y1,m1)" "(y2,m2)" n2 arbitrary: y2 m2 rule: months_later.induct)
    case Self
    thus "months_later (y0,m0) (y1,m1) (n1+0)"
      using `months_later (y0,m0) (y1,m1) n1` by simp
  next
    case (Later y1 m1 n y2 m2)
    hence
        "months_later (y0,m0) (y1,m1) (n1+n)"
        "(y2,m2) = next_month (y1,m1)"
      by simp+
    thus "months_later (y0,m0) (y2,m2) (n1+(Suc n))"
      using months_later.Later by force
  qed
qed

lemma months_later_year:
    "months_later (y,m) (y',m') n \<Longrightarrow> y' \<ge> y"
proof (induction "(y,m)" "(y',m')" n arbitrary: y' m' rule: months_later.induct)
  case Self
  thus "y >= y" by simp
next
  case (Later y1 m1 n y2 m2)
  hence
      "y1 \<ge> y"
      "(y2,m2) = next_month (y1,m1)"
    by simp+
  hence "y2 = y1 \<or> y2 = y1 + 1" using next_month_year_change by blast
  hence "y2 \<ge> y1" by auto
  thus "y2 \<ge> y" using `y1 \<ge> y` by simp
qed

lemma months_later_zero:
    "months_later (y,m) (y',m') 0 \<Longrightarrow> (y',m') = (y,m)"
  using months_later.simps
  by (metis Zero_not_Suc)

lemma months_later_left_bind:
    "months_later (y0,m0) (y2,m2) (Suc n)
    \<Longrightarrow> \<exists>y1. \<exists>m1. (y1,m1) = next_month (y0,m0) \<and> months_later (y1,m1) (y2,m2) n"
proof -
  assume "months_later (y0,m0) (y2,m2) (Suc n)"
  thus "\<exists>y1. \<exists>m1. (y1,m1) = next_month (y0,m0) \<and> months_later (y1,m1) (y2,m2) n"
  proof (induction n arbitrary: y2 m2)
    case 0
    hence "\<exists>y1'. \<exists>m1'. months_later (y0,m0) (y1',m1') 0 \<and> (y2,m2) = next_month (y1',m1')"
      using months_later.simps
      by (metis One_nat_def Suc_inject one_neq_zero)
    then obtain y1' m1' where
        "months_later (y0,m0) (y1',m1') 0"
        "(y2,m2) = next_month (y1',m1')"
      by auto
    hence "(y1',m1') = (y0,m0)" using months_later_zero by simp
    hence "(y2,m2) = next_month (y0,m0)" using `(y2,m2) = next_month (y1',m1')` by simp
    hence "(y2,m2) = next_month (y0,m0) \<and> months_later (y2,m2) (y2,m2) 0"
      using months_later.Self by blast
    thus "\<exists>y1. \<exists>m1. (y1,m1) = next_month (y0,m0) \<and> months_later (y1,m1) (y2,m2) 0" by blast
  next
    case assms: (Suc n)
    hence "\<exists>y1'. \<exists>m1'. months_later (y0,m0) (y1',m1') (Suc n) \<and> (y2,m2) = next_month (y1',m1')"
      using months_later.simps
      by (smt (verit) Suc_inject Zero_not_Suc)
    then obtain y1' m1' where
        "months_later (y0,m0) (y1',m1') (Suc n)"
        "(y2,m2) = next_month (y1',m1')"
      by auto
    hence "\<exists>y1. \<exists>m1. (y1,m1) = next_month (y0,m0) \<and> months_later (y1,m1) (y1',m1') n"
      using assms by simp
    then obtain y1 m1 where
        "(y1,m1) = next_month (y0,m0)"
        "months_later (y1,m1) (y1',m1') n"
      by auto
    hence "months_later (y1,m1) (y2,m2) (Suc n)"
      using
        `(y2,m2) = next_month (y1',m1')`
        months_later.Later
      by blast
    thus "\<exists>y1. \<exists>m1. (y1,m1) = next_month (y0,m0) \<and> months_later (y1,m1) (y2,m2) (Suc n)"
      using `(y1,m1) = next_month (y0,m0)` by blast
  qed
qed

lemma months_later_inverse_def:
    "months_later (y0,m0) (y1,m1) n
    \<Longrightarrow> (n = 0 \<and> (y0,m0) = (y1,m1))
        \<or> (\<exists>n' y1' m1'. n = (Suc n')
           \<and> months_later (y0,m0) (y1',m1') n'
           \<and> (y1,m1) = next_month (y1',m1'))"
  by (smt (verit, ccfv_SIG) months_later.simps)

lemma possible_months_later_in_year:
    "(months_later (y,December) (y,m) n
      \<longrightarrow> n = 0 \<and> m = December)
      \<and> (months_later (y,November) (y,m) n
        \<longrightarrow> (n = 0 \<and> m = November)
            \<or> (n > 0
              \<and> months_later (y,December) (y,m) (n-1)))
      \<and> (months_later (y,October) (y,m) n
        \<longrightarrow> (n = 0 \<and> m = October)
            \<or> (n > 0
              \<and> months_later (y,November) (y,m) (n-1)))
      \<and> (months_later (y,September) (y,m) n
        \<longrightarrow> (n = 0 \<and> m = September)
            \<or> (n > 0
              \<and> months_later (y,October) (y,m) (n-1)))
      \<and> (months_later (y,August) (y,m) n
        \<longrightarrow> (n = 0 \<and> m = August)
            \<or> (n > 0
              \<and> months_later (y,September) (y,m) (n-1)))
      \<and> (months_later (y,July) (y,m) n
        \<longrightarrow> (n = 0 \<and> m = July)
            \<or> (n > 0
              \<and> months_later (y,August) (y,m) (n-1)))
      \<and> (months_later (y,June) (y,m) n
        \<longrightarrow> (n = 0 \<and> m = June)
            \<or> (n > 0
              \<and> months_later (y,July) (y,m) (n-1)))
      \<and> (months_later (y,May) (y,m) n
        \<longrightarrow> (n = 0 \<and> m = May)
            \<or> (n > 0
              \<and> months_later (y,June) (y,m) (n-1)))
      \<and> (months_later (y,April) (y,m) n
        \<longrightarrow> (n = 0 \<and> m = April)
            \<or> (n > 0
              \<and> months_later (y,May) (y,m) (n-1)))
      \<and> (months_later (y,March) (y,m) n
        \<longrightarrow> (n = 0 \<and> m = March)
            \<or> (n > 0
              \<and> months_later (y,April) (y,m) (n-1)))
      \<and> (months_later (y,February) (y,m) n
        \<longrightarrow> (n = 0 \<and> m = February)
            \<or> (n > 0
              \<and> months_later (y,March) (y,m) (n-1)))
      \<and> (months_later (y,January) (y,m) n
        \<longrightarrow> (n = 0 \<and> m = January)
            \<or> (n > 0
              \<and> months_later (y,February) (y,m) (n-1)))"
proof -
  have
      "months_later (y,December) (y,m) n
      \<Longrightarrow> n = 0 \<and> m = December"
  proof -
    assume "months_later (y,December) (y,m) n"
    hence
        "(n = 0 \<and> (y,December) = (y,m))
          \<or> (\<exists>n' y' m'. n = (Suc n')
             \<and> months_later (y,December) (y',m') n'
             \<and> (y,m) = next_month (y',m'))"
      by (rule months_later_inverse_def)
    thus "n = 0 \<and> m = December"
    proof (elim disjE)
      assume "n = 0 \<and> (y,December) = (y,m)"
      thus "n = 0 \<and> m = December" by simp
    next
      assume assm:
          "\<exists>n' y' m'. n = Suc n'
          \<and> months_later (y,December) (y',m') n'
          \<and> (y,m) = next_month (y',m')"
      then obtain n' y' m' where
          "n = Suc n'"
          "months_later (y,December) (y',m') n'"
          "(y,m) = next_month (y',m')"
        by auto
      have "y' \<ge> y"
        using `months_later (y,December) (y',m') n'`
        by (rule months_later_year)
      have "y \<ge> y'"
        using
          `(y,m) = next_month (y',m')`
          next_month_year_change
        by fastforce
      hence "y = y'" using `y' \<ge> y` by simp
      have "n' = 0 \<or> n' > 0" by auto
      have "n' \<noteq> 0"
      proof
        assume "n' = 0"
        hence "m' = December"
          using
            `months_later (y,December) (y',m') n'`
            `y = y'`
            months_later_zero
          by blast
        hence "(y,m) = next_month (y,December)"
          using
            `y = y'`
            `(y,m) = next_month (y',m')`
          by simp
        thus False by simp
      qed
      then obtain n'' where
          "n' = (Suc n'')"
        using Nat.not0_implies_Suc by presburger
      hence
          "\<exists>y''. \<exists>m''. (y'',m'') = next_month (y,December)
          \<and> months_later (y'',m'') (y',m') n''"
        using
          `months_later (y,December) (y',m') n'`
          months_later_left_bind
        by blast
      then obtain y'' m'' where
          "(y'',m'') = next_month (y,December)"
          "months_later (y'',m'') (y',m') n''"
        by auto
      have "y' \<ge> y''"
        using `months_later (y'',m'') (y',m') n''`
        by (rule months_later_year)
      have "y'' = y' + 1"
        using
          `(y'',m'') = next_month (y,December)`
          `y = y'`
        by force
      hence False using `y' \<ge> y''` by simp
      thus ?thesis by simp
    qed
  qed
  moreover have
      "months_later (y,November) (y,m) n
      \<Longrightarrow> (n = 0 \<and> m = November)
      \<or> (n > 0 \<and> months_later (y,December) (y,m) (n-1))"
  proof -
    assume assm: "months_later (y,November) (y,m) n"
    have "n = 0 \<or> (\<exists>n'. n = Suc n')" by presburger
    thus ?thesis
    proof (elim disjE)
      assume "n = 0"
      hence "n = 0 \<and> m = November"
        using
          assm
          months_later_zero
        by blast
      thus ?thesis by simp
    next
      assume "\<exists>n'. n = Suc n'"
      then obtain n' where "n = Suc n'" by (rule HOL.exE)
      hence "n' = (n-1)" by simp
      have
          "\<exists>y'. \<exists>m'. (y',m') = next_month (y,November)
          \<and> months_later (y',m') (y,m) n'"
        using
          `n = Suc n'`
          `months_later (y,November) (y,m) n`
          months_later_left_bind
        by blast
      then obtain y' m' where
          "(y',m') = next_month (y,November)"
          "months_later (y',m') (y,m) n'"
        by auto
      hence "(y',m') = (y,December)"
        using `(y',m') = next_month (y,November)` by simp
      hence "months_later (y,December) (y,m) (n-1)"
        using
          `n' = (n-1)`
          `months_later (y',m') (y,m) n'`
        by blast
      thus ?thesis using `n = Suc n'` by fastforce
    qed
  qed
  moreover have
      "months_later (y,October) (y,m) n
      \<Longrightarrow> (n = 0 \<and> m = October)
      \<or> (n > 0 \<and> months_later (y,November) (y,m) (n-1))"
  proof -
    assume assm: "months_later (y,October) (y,m) n"
    have "n = 0 \<or> (\<exists>n'. n = Suc n')" by presburger
    thus ?thesis
    proof (elim disjE)
      assume "n = 0"
      hence "n = 0 \<and> m = October"
        using
          assm
          months_later_zero
        by blast
      thus ?thesis by simp
    next
      assume "\<exists>n'. n = Suc n'"
      then obtain n' where "n = Suc n'" by (rule HOL.exE)
      hence "n' = (n-1)" by simp
      have
          "\<exists>y'. \<exists>m'. (y',m') = next_month (y,October)
          \<and> months_later (y',m') (y,m) n'"
        using
          `n = Suc n'`
          `months_later (y,October) (y,m) n`
          months_later_left_bind
        by blast
      then obtain y' m' where
          "(y',m') = next_month (y,October)"
          "months_later (y',m') (y,m) n'"
        by auto
      hence "(y',m') = (y,November)"
        using `(y',m') = next_month (y,October)` by simp
      hence "months_later (y,November) (y,m) (n-1)"
        using
          `n' = (n-1)`
          `months_later (y',m') (y,m) n'`
        by blast
      thus ?thesis using `n = Suc n'` by fastforce
    qed
  qed
  moreover have
      "months_later (y,September) (y,m) n
      \<Longrightarrow> (n = 0 \<and> m = September)
      \<or> (n > 0 \<and> months_later (y,October) (y,m) (n-1))"
  proof -
    assume assm: "months_later (y,September) (y,m) n"
    have "n = 0 \<or> (\<exists>n'. n = Suc n')" by presburger
    thus ?thesis
    proof (elim disjE)
      assume "n = 0"
      hence "n = 0 \<and> m = September"
        using
          assm
          months_later_zero
        by blast
      thus ?thesis by simp
    next
      assume "\<exists>n'. n = Suc n'"
      then obtain n' where "n = Suc n'" by (rule HOL.exE)
      hence "n' = (n-1)" by simp
      have
          "\<exists>y'. \<exists>m'. (y',m') = next_month (y,September)
          \<and> months_later (y',m') (y,m) n'"
        using
          `n = Suc n'`
          `months_later (y,September) (y,m) n`
          months_later_left_bind
        by blast
      then obtain y' m' where
          "(y',m') = next_month (y,September)"
          "months_later (y',m') (y,m) n'"
        by auto
      hence "(y',m') = (y,October)"
        using `(y',m') = next_month (y,September)` by simp
      hence "months_later (y,October) (y,m) (n-1)"
        using
          `n' = (n-1)`
          `months_later (y',m') (y,m) n'`
        by blast
      thus ?thesis using `n = Suc n'` by fastforce
    qed
  qed
  moreover have
      "months_later (y,August) (y,m) n
      \<Longrightarrow> (n = 0 \<and> m = August)
      \<or> (n > 0 \<and> months_later (y,September) (y,m) (n-1))"
  proof -
    assume assm: "months_later (y,August) (y,m) n"
    have "n = 0 \<or> (\<exists>n'. n = Suc n')" by presburger
    thus ?thesis
    proof (elim disjE)
      assume "n = 0"
      hence "n = 0 \<and> m = August"
        using
          assm
          months_later_zero
        by blast
      thus ?thesis by simp
    next
      assume "\<exists>n'. n = Suc n'"
      then obtain n' where "n = Suc n'" by (rule HOL.exE)
      hence "n' = (n-1)" by simp
      have
          "\<exists>y'. \<exists>m'. (y',m') = next_month (y,August)
          \<and> months_later (y',m') (y,m) n'"
        using
          `n = Suc n'`
          `months_later (y,August) (y,m) n`
          months_later_left_bind
        by blast
      then obtain y' m' where
          "(y',m') = next_month (y,August)"
          "months_later (y',m') (y,m) n'"
        by auto
      hence "(y',m') = (y,September)"
        using `(y',m') = next_month (y,August)` by simp
      hence "months_later (y,September) (y,m) (n-1)"
        using
          `n' = (n-1)`
          `months_later (y',m') (y,m) n'`
        by blast
      thus ?thesis using `n = Suc n'` by fastforce
    qed
  qed
  moreover have
      "months_later (y,July) (y,m) n
      \<Longrightarrow> (n = 0 \<and> m = July)
      \<or> (n > 0 \<and> months_later (y,August) (y,m) (n-1))"
  proof -
    assume assm: "months_later (y,July) (y,m) n"
    have "n = 0 \<or> (\<exists>n'. n = Suc n')" by presburger
    thus ?thesis
    proof (elim disjE)
      assume "n = 0"
      hence "n = 0 \<and> m = July"
        using
          assm
          months_later_zero
        by blast
      thus ?thesis by simp
    next
      assume "\<exists>n'. n = Suc n'"
      then obtain n' where "n = Suc n'" by (rule HOL.exE)
      hence "n' = (n-1)" by simp
      have
          "\<exists>y'. \<exists>m'. (y',m') = next_month (y,July)
          \<and> months_later (y',m') (y,m) n'"
        using
          `n = Suc n'`
          `months_later (y,July) (y,m) n`
          months_later_left_bind
        by blast
      then obtain y' m' where
          "(y',m') = next_month (y,July)"
          "months_later (y',m') (y,m) n'"
        by auto
      hence "(y',m') = (y,August)"
        using `(y',m') = next_month (y,July)` by simp
      hence "months_later (y,August) (y,m) (n-1)"
        using
          `n' = (n-1)`
          `months_later (y',m') (y,m) n'`
        by blast
      thus ?thesis using `n = Suc n'` by fastforce
    qed
  qed
  moreover have
      "months_later (y,June) (y,m) n
      \<Longrightarrow> (n = 0 \<and> m = June)
      \<or> (n > 0 \<and> months_later (y,July) (y,m) (n-1))"
  proof -
    assume assm: "months_later (y,June) (y,m) n"
    have "n = 0 \<or> (\<exists>n'. n = Suc n')" by presburger
    thus ?thesis
    proof (elim disjE)
      assume "n = 0"
      hence "n = 0 \<and> m = June"
        using
          assm
          months_later_zero
        by blast
      thus ?thesis by simp
    next
      assume "\<exists>n'. n = Suc n'"
      then obtain n' where "n = Suc n'" by (rule HOL.exE)
      hence "n' = (n-1)" by simp
      have
          "\<exists>y'. \<exists>m'. (y',m') = next_month (y,June)
          \<and> months_later (y',m') (y,m) n'"
        using
          `n = Suc n'`
          `months_later (y,June) (y,m) n`
          months_later_left_bind
        by blast
      then obtain y' m' where
          "(y',m') = next_month (y,June)"
          "months_later (y',m') (y,m) n'"
        by auto
      hence "(y',m') = (y,July)"
        using `(y',m') = next_month (y,June)` by simp
      hence "months_later (y,July) (y,m) (n-1)"
        using
          `n' = (n-1)`
          `months_later (y',m') (y,m) n'`
        by blast
      thus ?thesis using `n = Suc n'` by fastforce
    qed
  qed
  moreover have
      "months_later (y,May) (y,m) n
      \<Longrightarrow> (n = 0 \<and> m = May)
      \<or> (n > 0 \<and> months_later (y,June) (y,m) (n-1))"
  proof -
    assume assm: "months_later (y,May) (y,m) n"
    have "n = 0 \<or> (\<exists>n'. n = Suc n')" by presburger
    thus ?thesis
    proof (elim disjE)
      assume "n = 0"
      hence "n = 0 \<and> m = May"
        using
          assm
          months_later_zero
        by blast
      thus ?thesis by simp
    next
      assume "\<exists>n'. n = Suc n'"
      then obtain n' where "n = Suc n'" by (rule HOL.exE)
      hence "n' = (n-1)" by simp
      have
          "\<exists>y'. \<exists>m'. (y',m') = next_month (y,May)
          \<and> months_later (y',m') (y,m) n'"
        using
          `n = Suc n'`
          `months_later (y,May) (y,m) n`
          months_later_left_bind
        by blast
      then obtain y' m' where
          "(y',m') = next_month (y,May)"
          "months_later (y',m') (y,m) n'"
        by auto
      hence "(y',m') = (y,June)"
        using `(y',m') = next_month (y,May)` by simp
      hence "months_later (y,June) (y,m) (n-1)"
        using
          `n' = (n-1)`
          `months_later (y',m') (y,m) n'`
        by blast
      thus ?thesis using `n = Suc n'` by fastforce
    qed
  qed
  moreover have
      "months_later (y,April) (y,m) n
      \<Longrightarrow> (n = 0 \<and> m = April)
      \<or> (n > 0 \<and> months_later (y,May) (y,m) (n-1))"
  proof -
    assume assm: "months_later (y,April) (y,m) n"
    have "n = 0 \<or> (\<exists>n'. n = Suc n')" by presburger
    thus ?thesis
    proof (elim disjE)
      assume "n = 0"
      hence "n = 0 \<and> m = April"
        using
          assm
          months_later_zero
        by blast
      thus ?thesis by simp
    next
      assume "\<exists>n'. n = Suc n'"
      then obtain n' where "n = Suc n'" by (rule HOL.exE)
      hence "n' = (n-1)" by simp
      have
          "\<exists>y'. \<exists>m'. (y',m') = next_month (y,April)
          \<and> months_later (y',m') (y,m) n'"
        using
          `n = Suc n'`
          `months_later (y,April) (y,m) n`
          months_later_left_bind
        by blast
      then obtain y' m' where
          "(y',m') = next_month (y,April)"
          "months_later (y',m') (y,m) n'"
        by auto
      hence "(y',m') = (y,May)"
        using `(y',m') = next_month (y,April)` by simp
      hence "months_later (y,May) (y,m) (n-1)"
        using
          `n' = (n-1)`
          `months_later (y',m') (y,m) n'`
        by blast
      thus ?thesis using `n = Suc n'` by fastforce
    qed
  qed
  moreover have
      "months_later (y,March) (y,m) n
      \<Longrightarrow> (n = 0 \<and> m = March)
      \<or> (n > 0 \<and> months_later (y,April) (y,m) (n-1))"
  proof -
    assume assm: "months_later (y,March) (y,m) n"
    have "n = 0 \<or> (\<exists>n'. n = Suc n')" by presburger
    thus ?thesis
    proof (elim disjE)
      assume "n = 0"
      hence "n = 0 \<and> m = March"
        using
          assm
          months_later_zero
        by blast
      thus ?thesis by simp
    next
      assume "\<exists>n'. n = Suc n'"
      then obtain n' where "n = Suc n'" by (rule HOL.exE)
      hence "n' = (n-1)" by simp
      have
          "\<exists>y'. \<exists>m'. (y',m') = next_month (y,March)
          \<and> months_later (y',m') (y,m) n'"
        using
          `n = Suc n'`
          `months_later (y,March) (y,m) n`
          months_later_left_bind
        by blast
      then obtain y' m' where
          "(y',m') = next_month (y,March)"
          "months_later (y',m') (y,m) n'"
        by auto
      hence "(y',m') = (y,April)"
        using `(y',m') = next_month (y,March)` by simp
      hence "months_later (y,April) (y,m) (n-1)"
        using
          `n' = (n-1)`
          `months_later (y',m') (y,m) n'`
        by blast
      thus ?thesis using `n = Suc n'` by fastforce
    qed
  qed
  moreover have
      "months_later (y,February) (y,m) n
      \<Longrightarrow> (n = 0 \<and> m = February)
      \<or> (n > 0 \<and> months_later (y,March) (y,m) (n-1))"
  proof -
    assume assm: "months_later (y,February) (y,m) n"
    have "n = 0 \<or> (\<exists>n'. n = Suc n')" by presburger
    thus ?thesis
    proof (elim disjE)
      assume "n = 0"
      hence "n = 0 \<and> m = February"
        using
          assm
          months_later_zero
        by blast
      thus ?thesis by simp
    next
      assume "\<exists>n'. n = Suc n'"
      then obtain n' where "n = Suc n'" by (rule HOL.exE)
      hence "n' = (n-1)" by simp
      have
          "\<exists>y'. \<exists>m'. (y',m') = next_month (y,February)
          \<and> months_later (y',m') (y,m) n'"
        using
          `n = Suc n'`
          `months_later (y,February) (y,m) n`
          months_later_left_bind
        by blast
      then obtain y' m' where
          "(y',m') = next_month (y,February)"
          "months_later (y',m') (y,m) n'"
        by auto
      hence "(y',m') = (y,March)"
        using `(y',m') = next_month (y,February)` by simp
      hence "months_later (y,March) (y,m) (n-1)"
        using
          `n' = (n-1)`
          `months_later (y',m') (y,m) n'`
        by blast
      thus ?thesis using `n = Suc n'` by fastforce
    qed
  qed
  moreover have
      "months_later (y,January) (y,m) n
      \<Longrightarrow> (n = 0 \<and> m = January)
      \<or> (n > 0 \<and> months_later (y,February) (y,m) (n-1))"
  proof -
    assume assm: "months_later (y,January) (y,m) n"
    have "n = 0 \<or> (\<exists>n'. n = Suc n')" by presburger
    thus ?thesis
    proof (elim disjE)
      assume "n = 0"
      hence "n = 0 \<and> m = January"
        using
          assm
          months_later_zero
        by blast
      thus ?thesis by simp
    next
      assume "\<exists>n'. n = Suc n'"
      then obtain n' where "n = Suc n'" by (rule HOL.exE)
      hence "n' = (n-1)" by simp
      have
          "\<exists>y'. \<exists>m'. (y',m') = next_month (y,January)
          \<and> months_later (y',m') (y,m) n'"
        using
          `n = Suc n'`
          `months_later (y,January) (y,m) n`
          months_later_left_bind
        by blast
      then obtain y' m' where
          "(y',m') = next_month (y,January)"
          "months_later (y',m') (y,m) n'"
        by auto
      hence "(y',m') = (y,February)"
        using `(y',m') = next_month (y,January)` by simp
      hence "months_later (y,February) (y,m) (n-1)"
        using
          `n' = (n-1)`
          `months_later (y',m') (y,m) n'`
        by blast
      thus ?thesis using `n = Suc n'` by fastforce
    qed
  qed
  ultimately show ?thesis by simp
qed

lemma next_month_excludes_later:
    "(y1,m1) = next_month (y0,m0)
    \<Longrightarrow> \<not> (\<exists>n. months_later (y1,m1) (y0,m0) n)"
proof -
  assume "(y1,m1) = next_month (y0,m0)"
  hence "m1 \<noteq> m0" by (rule next_month_month_change)
  have "months_later (y0,m0) (y1,m1) 1"
    using
      `(y1,m1) = next_month (y0,m0)`
      months_later.Later
      months_later.Self
    by force
  hence "y1 \<ge> y0" by (rule months_later_year)
  show "\<not> (\<exists>n. months_later (y1,m1) (y0,m0) n)"
  proof
    assume "\<exists>n. months_later (y1,m1) (y0,m0) n"
    then obtain n where "months_later (y1,m1) (y0,m0) n"
      by (rule HOL.exE)
    hence "y1 = y0"
      using
        `y1 \<ge> y0`
        months_later_year
      by fastforce
    hence "n \<noteq> 0"
      using
        `(y1,m1) = next_month (y0,m0)`
        `months_later (y1,m1) (y0,m0) n`
        `m1 \<noteq> m0`
        months_later_zero
        next_month_month_change
      by metis
    show False
    proof (cases m0)
      case December
      hence "(y1,m1) = (y0+1,January)"
        using `(y1,m1) = next_month (y0,m0)` by simp
      hence "y0+1 = y0" using `y1 = y0` by simp
      thus False by simp
    next
      case November
      hence "m1 = December"
        using `(y1,m1) = next_month (y0,m0)` by simp
      hence "months_later (y0,December) (y0,m0) n"
        using
          `months_later (y1,m1) (y0,m0) n`
          `y1 = y0`
        by simp
      hence "n = 0"
        using possible_months_later_in_year
        by simp
      thus False using `n \<noteq> 0` by contradiction
    next
      case October
      hence "m1 = November"
        using `(y1,m1) = next_month (y0,m0)` by simp
      hence "months_later (y0,November) (y0,m0) n"
        using
          `months_later (y1,m1) (y0,m0) n`
          `y1 = y0`
        by blast
      hence "m0 = December"
        using
          possible_months_later_in_year
          `n \<noteq> 0`
        by meson
      thus False using `m0 = October` by simp
    next
      case September
      hence "m0 = September" by simp
      hence "m1 = October"
        using `(y1,m1) = next_month (y0,m0)` by simp
      hence "months_later (y0,October) (y0,m0) n"
        using
          `months_later (y1,m1) (y0,m0) n`
          `y1 = y0`
        by blast
      hence "months_later (y0,November) (y0,m0) (n-1)"
        using
          possible_months_later_in_year
          `n \<noteq> 0`
        by auto
      hence "(y0,October) = next_month (y0,November)"
        using
          `m0 = September`
          possible_months_later_in_year
          Month.distinct
          Month.simps
        by metis
      thus False by simp
    next
      case August
      hence "m0 = August" by simp
      hence "m1 = September"
        using `(y1,m1) = next_month (y0,m0)` by simp
      hence "months_later (y0,September) (y0,m0) n"
        using
          `months_later (y1,m1) (y0,m0) n`
          `y1 = y0`
        by blast
      hence "months_later (y0,October) (y0,m0) (n-1)"
        using
          possible_months_later_in_year
          `n \<noteq> 0`
        by auto
      hence "(y0,September) = next_month (y0,October)"
        using
          `m0 = August`
          possible_months_later_in_year
          Month.distinct
          Month.simps
        by metis
      thus False by simp
    next
      case July
      hence "m0 = July" by simp
      hence "m1 = August"
        using `(y1,m1) = next_month (y0,m0)` by simp
      hence "months_later (y0,August) (y0,m0) n"
        using
          `months_later (y1,m1) (y0,m0) n`
          `y1 = y0`
        by blast
      hence "months_later (y0,September) (y0,m0) (n-1)"
        using
          possible_months_later_in_year
          `n \<noteq> 0`
        by auto
      hence "(y0,August) = next_month (y0,September)"
        using
          `m0 = July`
          possible_months_later_in_year
          Month.distinct
          Month.simps
        by metis
      thus False by simp
    next
      case June
      hence "m0 = June" by simp
      hence "m1 = July"
        using `(y1,m1) = next_month (y0,m0)` by simp
      hence "months_later (y0,July) (y0,m0) n"
        using
          `months_later (y1,m1) (y0,m0) n`
          `y1 = y0`
        by blast
      hence "months_later (y0,August) (y0,m0) (n-1)"
        using
          possible_months_later_in_year
          `n \<noteq> 0`
        by auto
      hence "(y0,July) = next_month (y0,August)"
        using
          `m0 = June`
          possible_months_later_in_year
          Month.distinct
          Month.simps
        by metis
      thus False by simp
    next
      case May
      hence "m0 = May" by simp
      hence "m1 = June"
        using `(y1,m1) = next_month (y0,m0)` by simp
      hence "months_later (y0,June) (y0,m0) n"
        using
          `months_later (y1,m1) (y0,m0) n`
          `y1 = y0`
        by blast
      hence "months_later (y0,July) (y0,m0) (n-1)"
        using
          possible_months_later_in_year
          `n \<noteq> 0`
        by auto
      hence "(y0,June) = next_month (y0,July)"
        using
          `m0 = May`
          possible_months_later_in_year
          Month.distinct
          Month.simps
        by metis
      thus False by simp
    next
      case April
      hence "m0 = April" by simp
      hence "m1 = May"
        using `(y1,m1) = next_month (y0,m0)` by simp
      hence "months_later (y0,May) (y0,m0) n"
        using
          `months_later (y1,m1) (y0,m0) n`
          `y1 = y0`
        by blast
      hence "months_later (y0,June) (y0,m0) (n-1)"
        using
          possible_months_later_in_year
          `n \<noteq> 0`
        by auto
      hence "(y0,May) = next_month (y0,June)"
        using
          `m0 = April`
          possible_months_later_in_year
          Month.distinct
          Month.simps
        by metis
      thus False by simp
    next
      case March
      hence "m0 = March" by simp
      hence "m1 = April"
        using `(y1,m1) = next_month (y0,m0)` by simp
      hence "months_later (y0,April) (y0,m0) n"
        using
          `months_later (y1,m1) (y0,m0) n`
          `y1 = y0`
        by blast
      hence "months_later (y0,May) (y0,m0) (n-1)"
        using
          possible_months_later_in_year
          `n \<noteq> 0`
        by auto
      hence "(y0,April) = next_month (y0,May)"
        using
          `m0 = March`
          possible_months_later_in_year
          Month.distinct
          Month.simps
        by metis
      thus False by simp
    next
      case February
      hence "m0 = February" by simp
      hence "m1 = March"
        using `(y1,m1) = next_month (y0,m0)` by simp
      hence "months_later (y0,March) (y0,m0) n"
        using
          `months_later (y1,m1) (y0,m0) n`
          `y1 = y0`
        by blast
      hence "months_later (y0,April) (y0,m0) (n-1)"
        using
          possible_months_later_in_year
          `n \<noteq> 0`
        by auto
      hence "(y0,March) = next_month (y0,April)"
        using
          `m0 = February`
          possible_months_later_in_year
          Month.distinct
          Month.simps
        by metis
      thus False by simp
    next
      case January
      hence "m0 = January" by simp
      hence "m1 = February"
        using `(y1,m1) = next_month (y0,m0)` by simp
      hence "months_later (y0,February) (y0,m0) n"
        using
          `months_later (y1,m1) (y0,m0) n`
          `y1 = y0`
        by blast
      hence "months_later (y0,March) (y0,m0) (n-1)"
        using
          possible_months_later_in_year
          `n \<noteq> 0`
        by auto
      hence "(y0,February) = next_month (y0,March)"
        using
          `m0 = January`
          possible_months_later_in_year
          Month.distinct
          Month.simps
        by metis
      thus False by simp
    qed
  qed
qed

lemma months_later_excludes_inverse_next_month:
    "months_later (y0,m0) (y1,m1) n \<Longrightarrow> (y0,m0) \<noteq> next_month (y1,m1)"
  using next_month_excludes_later by blast

lemma months_later_same:
    "months_later (y,m) (y,m) n \<Longrightarrow> n = 0"
  using
    months_later_inverse_def
    next_month_excludes_later
  by blast

theorem months_later_antisymmetry:
    "months_later (y,m) (y',m') n \<and> months_later (y',m') (y,m) n'
    \<Longrightarrow> (y',m') = (y,m)"
proof -
  assume assm: "months_later (y,m) (y',m') n \<and> months_later (y',m') (y,m) n'"
  hence "y' \<ge> y \<and> y \<ge> y'" using months_later_year by auto
  hence "y' = y" by simp
  have "n = 0 \<or> n > 0" by auto
  thus "(y',m') = (y,m)"
  proof (elim disjE)
    assume "n = 0"
    hence "months_later (y,m) (y',m') 0" using assm by simp
    thus "(y',m') = (y,m)" by (rule months_later_zero)
  next
    assume "n > 0"
    hence "\<exists>n''. n = Suc n''" by (rule Nat.gr0_implies_Suc)
    then obtain n'' where "n = Suc n''" by auto
    hence
        "\<exists>y'' m''. months_later (y,m) (y'',m'') n''
        \<and> (y',m') = next_month (y'',m'')"
      using
        assm
        months_later.Later
        months_later_inverse_def
      by fastforce
    then obtain y'' m'' where
        "months_later (y,m) (y'',m'') n''"
        "(y',m') = next_month (y'',m'')"
      by auto
    hence "\<not>(\<exists>n'''. months_later (y',m') (y'',m'') n''')"
      using next_month_excludes_later by simp
    have "months_later (y',m') (y'',m'') (n'+n'')"
      using
        assm 
        `months_later (y,m) (y'',m'') n''`
        months_later_sum
      by blast
    hence False
      using `\<not>(\<exists>n'''. months_later (y',m') (y'',m'') n''')`
      by simp
    thus "(y',m') = (y,m)" by simp
  qed
qed

end
