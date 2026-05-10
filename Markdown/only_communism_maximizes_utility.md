---
title: "Pure communism is the only redistribution which maximizes the social utility"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - Economics
  - Taxation
...


## Presentation

Utility is a kind of index of satisfaction: it is a number such that, the higher it is, the more satisfied you are. Then the social utility is the sum of all individual utilities and constitutes a kind of global index of satisfaction.

The present article states that, essentially, if everyone is assigned the same (standard) utility, pure communism is the (single) redistribution which maximizes the social utility.

One relies on [this article](https://leibnizproject.com/Articles/definition_capitalism_communism.html).

--MATH_START--
Throughout this page, let $I$ be the finite set of individuals (with $N$ as the number of individuals) and $gs \in \mathbb R$ is governement spending.
--MATH_END--

[//]: # Lean4 (7-9)


## Utility

The more money you receive, the more you are satisfied: utility increases with money.

--MATH_START--
$\mathbf{Definition}$\
The utility function $u: \mathbb R \to \mathbb R$ is said to increase with money if it is monotone.
--MATH_END--

[//]: # Lean4 (14-15)

You are more satisfied to get an extra euro when you already have only one euro than when you have 1000€.

--MATH_START--
$\mathbf{Definition}$\
The utility function $u: \mathbb R \to \mathbb R$ is said to (resp. strictly) satisfy the law of diminishing marginal utility if $u''$ is (resp. strictly) concave on ${\mathbb R}^+$.
--MATH_END--

[//]: # Lean4 (17-21)

The social utility is just of all individual utilities.

--MATH_START--
$\mathbf{Definition}$\
Let $u: \mathbb R \to \mathbb R$ be a utility function and $r : I \to \mathbb R$ be a profile of retributions given to individuals. \
The social utility of $u$ on $r$ is $\sum_{i \in I} u(r(i))$.
--MATH_END--

[//]: # Lean4 (23-24)


## Communism maximizes social utility

Pure communism is essentially the single redistribution maximizing the social utility.

--MATH_START--
$\mathbf{Proposition}$\
Let $u: \mathbb R \to \mathbb R$ be a utility function satisfying the law of diminishing marginal utility. \
Let $r : {\mathbb R}^I \to {\mathbb R}^I$ be a redistribution and $c \in {\mathbb R}^I$ be a retribution profile, such that all indivdual retributions are nonnegative (this hypothesis is here only in order to be able to apply the law of diminishing marginal utility which regards only positive retributions). \
Then the social utility on $r(c)$ is less or equal to the social utility with pure communism instead of $r$.

$\mathbf{proof:}$\
The social utility on $r(c)$ is $su = \sum_{i \in I} u(r(c)(i))$. \
$u$ being concave, by Jensen's inequality,
$$u(\frac {\sum_{i \in I} r(c)(i)} N) \ge \frac {\sum_{i \in I} u(r(c)(i))} N$$
So that
$$su \le N \times u(\frac {\sum_{i \in I} r(c)(i)} N)$$
By the equilibrium of accounts, $\sum_{i \in I} r(c)(i) = \sum_{i \in I} c(i) - gs$, so
$$su \le N \times u(\frac {(\sum_{i \in I} c(i)) - gs} N)$$
The right hand side of the inequality above is the social utility which would have occurred in pure communism. \
■

$\mathbf{Proposition}$\
Let $u: \mathbb R \to \mathbb R$ be a utility function strictly satisfying the law of diminishing marginal utility. \
Let $r : {\mathbb R}^I \to {\mathbb R}^I$ be a redistribution and $c \in {\mathbb R}^I$ be a retribution profile, such that all indivdual retributions are nonnegative. \
If the social utility on $r(c)$ equals to the social utility with pure communism instead of $r$ (that is if it is maximal), then $r$ coincides with pure communism on $c$.

$\mathbf{proof:}$\
If $r$ does not coincide with pure communism, there would two individual retributions.
So that, $u$ being strictly concave, by the strict version of Jensen's inequality,
$$u(\frac {\sum_{i \in I} r(c)(i)} N) \gt \frac {\sum_{i \in I} u(r(c)(i))} N$$
So that
$$\sum_{i \in I} u(r(c)(i)) \lt N \times u(\frac {\sum_{i \in I} r(c)(i)} N)$$
By the equilibrium of accounts, $\sum_{i \in I} r(c)(i) = \sum_{i \in I} c(i) - gs$, so
$$\sum_{i \in I} u(r(c)(i)) \lt N \times u(\frac {(\sum_{i \in I} c(i)) - gs} N)$$
Therefore the social utility on $r(c)$ (left-hand side of the inequality above) does not equal the social utility with pure communism instead of $r$ (right-hand side of the inequality above). \
■
--MATH_END--

[//]: # Lean4 (26-181)
