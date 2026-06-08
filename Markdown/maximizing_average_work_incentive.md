---
title: "Maximizing the average work incentive"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - Economics
  - Taxation
...


## Presentation

It is often asked and investigated how make people as keen as possible to work. \
If one fixes the maximization of the incentive to work (as defined in [this article](https://leibnizproject.com/Articles/definition_capitalism_communism.html)) as a desirable goal, pure capitalisms (also defined [here](https://leibnizproject.com/Articles/definition_capitalism_communism.html)) unsurprisingly maximize this incentive (under certain conditions), but they are far from being the only ones.

--MATH_START--
Throughout this page, let $I$ be the finite set of individuals (with $N$ as the number of individuals) and $gs \in \mathbb R$ is governement spending.
--MATH_END--

[//]: # Lean4 (14-16)


## Average work incentive

The work incentive of an individual depends on the situation, so we consider its average over all these situations.

--MATH_START--
$\mathbf{Definition}$\
Let $r: {\mathbb R}^I \to {\mathbb R}^I$ be a redistribution. \
Let $i \in I$ be an individual. \
Let $c \in {\mathbb R}^I$ be a contribution profile. \
Let $a, b \in {\mathbb R}$ be quantities (representing individual contributions) such that $a \lt b$. \
The average work incentive for $i$ between $a$ and $b$ is
$$awi(a, b) = \frac {r(c_{i \leftarrow b})(i) - r(c_{i \leftarrow a})(i)} {b - a}$$
--MATH_END--

[//]: # Lean4 (21-28)

--MATH_START--
$\mathbf{Lemma}$\
Let $r: {\mathbb R}^I \to {\mathbb R}^I$ be a redistribution. \
Let $i \in I$ be an individual. \
Let $c \in {\mathbb R}^I$ be a contribution profile. \
Let $a, b \in {\mathbb R}$ be quantities (representing individual contributions) such that $a \lt b$. \
If $wi = \frac {\mathrm{d} r(c_{i \leftarrow q})(i)} {\mathrm{d} q}$ is the work incentive of individual $i$, the average work incentive $awi(a, b)$ equals the following term (if it's well defined):
$$\frac 1 {b - a} \int_{a}^{b} wi(q) \, dq$$

$\mathbf{proof:}$\
This is a straight enforcement of the fundamental theorem of calculus. \
■
--MATH_END--

[//]: # Lean4 (30-58)

--MATH_START--
$\mathbf{Definition}$\
Let $r: {\mathbb R}^I \to {\mathbb R}^I$ be a redistribution. \
Let $i \in I$ be an individual. \
Let $c \in {\mathbb R}^I$ be a contribution profile. \
Then: \
- the average work incentive for positive contributions of $i$ is $awi_+ = \lim_{M \to +\infty} awi(0, M)$ \
- the average work incentive for negative contributions of $i$ is $awi_- = \lim_{m \to -\infty} awi(m, 0)$ \
- the (global) average work incentive of $i$ is defined as $awi = \frac {awi_+ + awi_-} 2$ \
Any of these quantities may not exist.
--MATH_END--

[//]: # Lean4 (60-104)


## Maximizing the average work incentive

It does not seem unreasonable to assume that an individual can not by contributing a lot make the other individuals' average earning less than 0. \
The inverse would be quite weird. Supposing this permits to conclude that the average work incentive for an individual contributing positively (that is working, not destructing) can not exceed 1.

--MATH_START--
$\mathbf{Definition}$\
Let $r: {\mathbb R}^I \to {\mathbb R}^I$ be a redistribution. \
Let $i \in I$ be an individual. \
Let $c \in {\mathbb R}^I$ be a contribution profile. \
It is said that the sum of retributions of all the individuals but $i$ is nonnegative from a certain contribution $M_0$ by $i$ if
$$\forall M \ge M_0, 0 \le \sum_{j \ne i} r(c_{i \leftarrow M})(j)$$

$\mathbf{Proposition-Definition}$\
Let $r: {\mathbb R}^I \to {\mathbb R}^I$ be a redistribution. \
Let $i \in I$ be an individual. \
Let $c \in {\mathbb R}^I$ be a contribution profile. \
Let's suppose that: \
- the average work incentive for positive contributions of $i$ exists (let's denote it $awi_+$) \
- the sum of retributions of all the individuals but $i$ is nonnegative from a certain contribution by $i$ \
Then $awi_+ \le 1$. In such a case, $r$ is said to maximize the average work incentive for positive contributions.

$\mathbf{proof:}$\
$awi_+ = \lim_{M \to +\infty} \frac {r(c_{i \leftarrow M})(i) - r(c_{i \leftarrow 0})(i)} M$ \
By the account equilibrium, we have $\sum_{j \in I} c_{i \leftarrow M}(j) = gs + \sum_{j \in I} r(c_{i \leftarrow M})(j)$, so that
$$\sum_{j \ne i} c(j) + M = gs + \sum_{j \ne i} r(c_{i \leftarrow M})(j) + r(c_{i \leftarrow M})(i)$$ and
$$r(c_{i \leftarrow M})(i) = \sum_{j \ne i} c(j) + M - gs - \sum_{j \ne i} r(c_{i \leftarrow M})(j)$$
By substitution, \
$$awi_+ = \lim_{M \to +\infty} \frac {\sum_{j \ne i} c(j) + M - gs - \sum_{j \ne i} r(c_{i \leftarrow M})(j) - r(c_{i \leftarrow 0})(i)} M$$ \
As the sum of retributions of all the individuals but $i$ is nonnegative from a certain contribution by $i$,
$$awi_+ \le \lim_{M \to +\infty} \frac {\sum_{j \ne i} c(j) + M - gs - r(c_{i \leftarrow 0})(i)} M$$
which is $1$. \
■
--MATH_END--

[//]: # Lean4 (106-303)

The second hypothesis is rather technical. To be honest, it is designed to get quickly rid of the case of negative contributions (that is individuals who cost to the society instead of contributing to it), having in mind that it's supposed to be marginal. \
To state it grossly, if some kind of massively destructing individual is able to generate much damage, the impact on the retributions of other individuals tends to be negligible (compared to the amount of this damage).

--MATH_START--
$\mathbf{Definition}$\
Let $r: {\mathbb R}^I \to {\mathbb R}^I$ be a redistribution. \
Let $i \in I$ be an individual. \
Let $c \in {\mathbb R}^I$ be a contribution profile. \
It is said that $i$'s contribution at bottom dominates the sum of other retributions if
$$\lim_{m \to -\infty} \frac {\sum_{j \ne i} r(c_{i \leftarrow m})(j)} m = 0$$

$\mathbf{Proposition-Definition}$\
Let $r: {\mathbb R}^I \to {\mathbb R}^I$ be a redistribution. \
Let $i \in I$ be an individual. \
Let $c \in {\mathbb R}^I$ be a contribution profile. \
If $i$'s contribution at bottom dominates the sum of other retributions, then the average work incentive for negative contributions of $i$ is $1$.

$\mathbf{proof:}$\
$awi_- = \lim_{m \to -\infty} \frac {r(c_{i \leftarrow 0})(i) - r(c_{i \leftarrow m})(i)} {0 - m}$ \
By the account equilibrium, we have $\sum_{j \in I} c_{i \leftarrow m}(j) = gs + \sum_{j \in I} r(c_{i \leftarrow m})(j)$, so that
$$\sum_{j \ne i} c(j) + m = gs + \sum_{j \ne i} r(c_{i \leftarrow m})(j) + r(c_{i \leftarrow m})(i)$$ and
$$r(c_{i \leftarrow m})(i) = \sum_{j \ne i} c(j) + m - gs - \sum_{j \ne i} r(c_{i \leftarrow m})(j)$$
By substitution, \
$$\begin{align}
  awi_- &= \lim_{m \to -\infty} \frac {r(c_{i \leftarrow 0}) - \sum_{j \ne i} c(j) - m +  gs + \sum_{j \ne i} r(c_{i \leftarrow m})(j)(i)} {-m} \\
        &= \lim_{m \to -\infty} \left( 1 - \frac {\sum_{j \ne i} r(c_{i \leftarrow m})(j)(i)} m + \frac {r(c_{i \leftarrow 0}) - \sum_{j \ne i} c(j) + gs} {-m} \right) \\
        &= 1
\end{align}$$
■
--MATH_END--

[//]: # Lean4 (305-467)

So that with those two hypotheses, the global average work incentive can not exceed 1.

--MATH_START--
$\mathbf{Corollary}$\
Let $r: {\mathbb R}^I \to {\mathbb R}^I$ be a redistribution. \
Let $i \in I$ be an individual. \
Let $c \in {\mathbb R}^I$ be a contribution profile. \
Let's suppose that: \
- the average work incentive for positive contributions of $i$ exists (let's denote it $awi_+$) \
- the sum of retributions of all the individuals but $i$ is nonnegative from a certain contribution by $i$ \
- $i$'s contribution at bottom dominates the sum of other retributions \
Then the global average work incentive exists and can't exceed $1$.

$\mathbf{proof:}$\
Immediate from the two previous results, plus the fact that $\forall x \in \mathbb R, x \le 1 \Rightarrow \frac {x + 1} 2 \le 1$. \
■

$\mathbf{Definition}$\
A redistribution is said to maximize the (global) average work incentive if it exists and equals $1$.
--MATH_END--

[//]: # Rocq (469-499)


## Examples of redistributions maximizing the average work incentive

Unsurprisingly, pure capitalisms maximize the average work incentive.

--MATH_START--
$\mathbf{Lemma}$\
The average work incentive of pure capiptalisms is $1$ (and thus they maximize it).

$\mathbf{proof:}$\
$$\begin{align}
  awi &= awi_+ + awi_- \\
      &= \frac {\lim_{M \to +\infty} \frac {r(c_{i \leftarrow M})(i) - r(c_{i \leftarrow 0})(i)} M + \lim_{m \to -\infty} \frac {r(c_{i \leftarrow 0})(i) - r(c_{i \leftarrow m})(i)} {0 - m}} 2 \\
      &= \frac {\lim_{M \to +\infty} \frac {M - \frac {gs} N - r(c_{i \leftarrow 0})(i)} M + \lim_{m \to -\infty} \frac {r(c_{i \leftarrow 0})(i) - m + \frac {gs} N} {-m}} 2 \\
      &= \frac {1 + 1} 2 = 1
\end{align}$$
■
--MATH_END--

[//]: # Lean4 (501-567)

A bit less intuitively, a society which retributes \
- both the greatest and the least contributor up to their contribution and all the other individuals \
- all the other individuals equally, whatever their contribution \
also maximizes the average work incentive.

--MATH_START--
$\mathbf{Definition}$\
Let $i \in I$ be an individual. \
Let $c \in {\mathbb R}^I$ be a contribution profile. \
$i$ is said to be a greatest contributor if $\forall j \in I, c(j) \le c(i)$ \
$i$ is said to be a least contributor if $\forall j \in I, c(j) \ge c(i)$ \
$i$ is said to be the (single) greatest contributor if it's a greatest contributor and $\forall j \in I, c(j) = c(i) \Rightarrow j = i$ \
$i$ is said to be the (single) least contributor if it's a least contributor and $\forall j \in I, c(j) = c(i) \Rightarrow j = i$
--MATH_END--

[//]: # Lean4 (569-636)

--MATH_START--
$\mathbf{Proposition-Definition}$\
Communism except for extremal contributors is the function $ceec$ defined by
$$\begin{align*}
  {\mathbb R}^I &\to {\mathbb R}^I\\
  c &\mapsto \left({i_0 \in I} \mapsto \begin{cases*}
    c(i) \text{ if } i_0 \text{ is the single greatest contributor or the single least contributor} \\
    \frac {(\sum_{i\text{ neither single greatest nor single least contributor}} c(i)) - gs} {\#\{i\text{ neither single greatest nor single least contributor}\}} \text{ otherwise}
  \end{cases*}\right)
\end{align*}$$
If $N \ge 3$, accounts are at equilibrium and thus defines a redistribution.

$\mathbf{proof:}$\
Let $c \in {\mathbb R}^I$. \
<u>Case 1</u>: there is neither a single greatest contributor nor a least one \
$$\begin{align}
  gs + \sum_{i \in I} ceec(c)(i) &= gs + N \times \left(\frac {(\sum_{i \in I} c(i)) - gs} {\#I}\right) \\
                                 &= \sum_{i \in I} c(i)
\end{align}$$
<u>Case 2</u>: there is a single greatest contributor $i_M$ but no least one \
$$\begin{align}
  gs + \sum_{i \in I} ceec(c)(i) &= gs + c(i_M) + (N - 1) \times \left(\frac {(\sum_{i \ne i_M} c(i)) - gs} {\#(I - \{i_M\})}\right) \\
                                 &= c(i_M) + \sum_{i \ne i_M} c(i) \\
                                 &= \sum_{i \in I} c(i)
\end{align}$$
<u>Case 3</u>: there is a single least contributor $i_m$ but no greatest one \
$$\begin{align}
  gs + \sum_{i \in I} ceec(c)(i) &= gs + c(i_m) + (N - 1) \times \left(\frac {(\sum_{i \ne i_m} c(i)) - gs} {\#(I - \{i_m\})}\right) \\
                                 &= c(i_m) + \sum_{i \ne i_m} c(i) \\
                                 &= \sum_{i \in I} c(i)
\end{align}$$
<u>Case 4</u>: there is a single greatest contributor $i_M$ and a least one $i_m$ \
$$\begin{align}
  gs + \sum_{i \in I} ceec(c)(i) &= gs + c(i_M) + c(i_m) + (N - 2) \times \left(\frac {(\sum_{i \ne i_M, i_m} c(i)) - gs} {\#(I - \{i_M, i_m\})}\right) \\
                                 &= c(i_M) + c(i_m) + \sum_{i \ne i_M, i_m} c(i) \\
                                 &= \sum_{i \in I} c(i)
\end{align}$$
■
--MATH_END--

[//]: # Lean4 (638-1279)

--MATH_START--
$\mathbf{Lemma}$\
Communism except for extremal contributors has $1$ as average work incentive (and thus it maximizes it).

$\mathbf{proof:}$\
$$\begin{align}
  awi &= awi_+ + awi_- \\
      &= \frac {\lim_{M \to +\infty} \frac {r(c_{i \leftarrow M})(i) - r(c_{i \leftarrow 0})(i)} M + \lim_{m \to -\infty} \frac {r(c_{i \leftarrow 0})(i) - r(c_{i \leftarrow m})(i)} {0 - m}} 2 \\
      &= \frac {\lim_{M \to +\infty} \frac {M - r(c_{i \leftarrow 0})(i)} M + \lim_{m \to -\infty} \frac {r(c_{i \leftarrow 0})(i) - m} {-m}} 2 \\
      &= \frac {1 + 1} 2 = 1
\end{align}$$
■
--MATH_END--

[//]: # Lean4 (1281-1493)
