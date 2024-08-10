theory Days_In_Month
imports Month
begin

fun "leap_year" :: "Year \<Rightarrow> bool" where
	"leap_year y =
	(y mod 4 = 0 \<and> (y mod 100 \<noteq> 0 \<or> y mod 400 = 0))"

fun days_in_month :: "Year \<times> Month \<Rightarrow> nat" where
  "days_in_month (y,January) = 31" |
  "days_in_month (y,February) =
    (if leap_year y then 29 else 28)" |
  "days_in_month (y,March) = 31" |
  "days_in_month (y,April) = 30" |
  "days_in_month (y,May) = 31" |
  "days_in_month (y,June) = 30" |
  "days_in_month (y,July) = 31" |
  "days_in_month (y,August) = 31" |
  "days_in_month (y,September) = 30" |
  "days_in_month (y,October) = 31" |
  "days_in_month (y,November) = 30" |
  "days_in_month (y,December) = 31"

inductive days_in_months :: "Year \<times> Month \<Rightarrow> Year \<times> Month \<Rightarrow> nat \<Rightarrow> bool" where
Self: "days_in_months (y,m) (y,m) (days_in_month (y,m))" |
Next:
  "days_in_months (y0,m0) (y1,m1) c1 \<and> (y2,m2) = next_month (y1,m1)
  \<Longrightarrow> days_in_months (y0,m0) (y2,m2) (c1 + days_in_month (y2,m2))"

lemma days_in_months_iff_months_later:
    "(\<exists>n. days_in_months (y,m) (y',m') n)
    \<longleftrightarrow> (\<exists>n. months_later (y,m) (y',m') n)"
proof
  assume "\<exists>n. days_in_months (y,m) (y',m') n"
  then obtain nd where
      "days_in_months (y,m) (y',m') nd"
    by (rule HOL.exE)
  thus "\<exists>n. months_later (y,m) (y',m') n"
  proof (induction)
    case (Self y m)
    hence "months_later (y,m) (y,m) 0"
      by (rule months_later.Self)
    thus ?case by (rule HOL.exI)
  next
    case (Next y0 m0 y1 m1 c1 y2 m2)
    hence
        "days_in_months (y0,m0) (y1,m1) c1"
        "\<exists>n. months_later (y0,m0) (y1,m1) n"
        "(y2,m2) = next_month (y1,m1)"
      by simp+
    then obtain nm where
        "months_later (y0,m0) (y1,m1) nm"
      by auto
    hence "months_later (y0,m0) (y2,m2) (Suc nm)"
      using
        `(y2,m2) = next_month (y1,m1)`
        months_later.Later
      by simp
    thus ?case by (rule HOL.exI)
  qed
next
  assume "\<exists>n. months_later (y,m) (y',m') n"
  then obtain nm where
      "months_later (y,m) (y',m') nm"
    by (rule HOL.exE)
  thus "\<exists>n. days_in_months (y,m) (y',m') n"
  proof (induction)
    case (Self y m)
    hence "days_in_months (y,m) (y,m) (days_in_month (y,m))"
      by (rule days_in_months.Self)
    thus ?case by (rule HOL.exI)
  next
    case (Later y0 m0 y1 m1 nm y2 m2)
    hence
        "months_later (y0,m0) (y1,m1) nm"
        "\<exists>n. days_in_months (y0,m0) (y1,m1) n"
        "(y2,m2) = next_month (y1,m1)"
      by simp+
    then obtain nd where
        "days_in_months (y0,m0) (y1,m1) nd"
      by auto
    hence
        "days_in_months (y0,m0) (y2,m2) (nd + days_in_month (y2,m2))"
      using
        `(y2,m2) = next_month (y1,m1)`
        days_in_months.Next
      by simp
    thus ?case by (rule HOL.exI)
  qed
qed

lemma days_in_months_unique:
    "days_in_months (y0,m0) (y1,m1) n0 \<and> days_in_months (y0,m0) (y1,m1) n1
    \<Longrightarrow> n1 = n0"
proof -
  assume "days_in_months (y0,m0) (y1,m1) n0 \<and> days_in_months (y0,m0) (y1,m1) n1"
  hence
      "days_in_months (y0,m0) (y1,m1) n0"
      "days_in_months (y0,m0) (y1,m1) n1"
    by simp+
  thus "n1 = n0"
  proof (induction arbitrary: n1)
    case (Self y m)
    hence "days_in_months (y,m) (y,m) n1" by simp
    hence
        "n1 = days_in_month (y,m)
        \<or> (\<exists>y' m'. days_in_months
                      (y,m)
                      (y',m')
                      (n1 - days_in_month (y,m))
          \<and> (y,m) = next_month (y',m'))"
    proof (cases rule: days_in_months.cases)
      case Self
      hence "n1 = days_in_month (y,m)" by simp
      thus ?thesis by simp
    next
      case (Next y' m' n')
      hence
          "n1 = n' + days_in_month (y,m)"
          "days_in_months (y,m) (y',m') n'"
          "(y,m) = next_month (y',m')"
        by simp+
      hence "n' = n1 - days_in_month (y,m)" by simp
      hence
          "days_in_months (y,m) (y',m') (n1 - days_in_month (y,m))
          \<and> (y,m) = next_month (y',m')"
        using
          `days_in_months (y,m) (y',m') n'`
          `(y,m) = next_month (y',m')`
        by simp
      thus ?thesis
        using
          days_in_months_iff_months_later
          next_month_excludes_later
        by blast
    qed
    show ?case
    proof (rule ccontr)
      assume "n1 \<noteq> days_in_month (y,m)"
      hence
          "\<exists>y' m'. days_in_months
                    (y,m)
                    (y',m')
                    (n1 - days_in_month (y,m))
          \<and> (y,m) = next_month (y',m')"
        using
          `n1 = days_in_month (y,m)
          \<or> (\<exists>y' m'. days_in_months
                      (y,m)
                      (y',m')
                      (n1 - days_in_month (y,m))
             \<and> (y,m) = next_month (y',m'))`
        by blast
      then obtain y' m' where
          "days_in_months (y,m) (y',m') (n1 - days_in_month (y,m))"
          "(y,m) = next_month (y',m')"
        by auto
      hence "\<exists>n. months_later (y,m) (y',m') n"
        using days_in_months_iff_months_later by blast
      thus False
        using
          `(y,m) = next_month (y',m')`
          next_month_excludes_later
        by blast
    qed
  next
    case (Next y0 m0 y1 m1 c1 y2 m2)
    hence
        "days_in_months (y0,m0) (y1,m1) c1"
        "\<forall>c2. days_in_months (y0,m0) (y1,m1) c2 \<longrightarrow> c1 = c2"
        "(y2,m2) = next_month (y1,m1)"
        "days_in_months (y0,m0) (y2,m2) n1"
      by simp+
    hence "\<exists>n. months_later (y0,m0) (y1,m1) n"
      using days_in_months_iff_months_later by blast
    then obtain nm where "months_later (y0,m0) (y1,m1) nm" by (rule HOL.exE)
    hence "months_later (y0,m0) (y2,m2) (Suc nm)"
      using
        `(y2,m2) = next_month (y1,m1)`
        months_later.Later
      by simp
    show "n1 = c1 + days_in_month (y2,m2)"
      sorry
  qed

lemma days_in_months_left_bind:
    "days_in_months (y0,m0) (y1,m1) n
    \<Longrightarrow> (y1,m1) = (y0,m0)
        \<or> (\<exists>y0' m0'. (y0',m0') = next_month (y0,m0)
           \<and> days_in_months
              (y0',m0')
              (y1,m1)
              (n - days_in_month (y0,m0)))"
proof -
  assume "days_in_months (y0,m0) (y1,m1) n"
  thus ?thesis
  proof (induction)
    case (Self y m)
    hence "(y,m) = (y,m)" by simp
    thus ?case by simp
  next
    case (Next y0 m0 y1 m1 n y2 m2)
    hence
        "days_in_months (y0,m0) (y1,m1) n"
        "(y1,m1) = (y0,m0)
        \<or> (\<exists>y0' m0'. (y0',m0') = next_month (y0,m0)
           \<and> days_in_months
              (y0',m0')
              (y1,m1)
              (n - days_in_month (y0,m0)))"
        "(y2,m2) = next_month (y1,m1)"
      by simp+
    have "(y1,m1) = (y0,m0) \<or> (y1,m1) \<noteq> (y0,m0)" by simp
    hence
        "\<exists>y0' m0'. (y0',m0') = next_month (y0,m0)
        \<and> days_in_months
            (y0',m0')
            (y2,m2)
            (n + days_in_month (y2,m2) - days_in_month (y0,m0))"
    proof (elim disjE)
      assume "(y1,m1) = (y0,m0)"
      hence "days_in_months (y0,m0) (y1,m1) (days_in_month (y0,m0))"
        using days_in_months.Self by presburger
      hence "n - days_in_month (y0,m0) = 0" try
    thus ?case by simp
  qed

lemma days_in_years:
    "(y+1,m) = next_month (y',m')
    \<Longrightarrow> days_in_months (y,m) (y',m') 365
    \<or> days_in_months (y,m) (y',m') 366"
proof -
  assume "(y+1,m) = next_month (y',m')"
  have "m' = January \<or> m' \<noteq> January" by simp
  thus "days_in_months (y,m) (y',m') 365 \<or> days_in_months (y,m) (y',m') 366"
  proof (elim disjE)
    assume "m' = January"
    hence "m = February"
      using `(y+1,m) = next_month (y',m')` by simp
    have "leap_year y \<or> \<not> leap_year y" by simp
    thus "days_in_months (y,m) (y',m') 365 \<or> days_in_months (y,m) (y',m') 366"
    proof (elim disjE)
      assume "leap_year y"
      hence "days_in_month (y,m) = 29"
        using `m = February` by simp
      hence "days_in_months (y,m) (y',m') 366" 
qed

end