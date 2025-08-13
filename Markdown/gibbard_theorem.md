---
title: "Gibbard's theorem"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - social choice
...


## Presentation

Here is [Gibbard's theorem](https://en.wikipedia.org/wiki/Gibbard's_theorem) and its immediate corollary [Gibbard–Satterthwaite theorem](https://en.wikipedia.org/wiki/Gibbard%E2%80%93Satterthwaite_theorem), which proves the impossibility of a perfect democracy, in the sense that voters can get a better outcome by casting an insincere ballot.

Let's say that at least 3 alternatives (candidates or policy measures) compete at an election. Each voter has a preference order (possibly with ties) on the alternatives and none of them can decide the issue regardless of the other votes. Then it is possible that the outcome  of a vote is more in line with a voter's preference when she's not sincere in her ballot (whatever the voting scheme, that is whatever the way to designate the winner of the election from votes).

The present article is mostly a copy of [Gibbard's original article](https://wayback.archive-it.org/5456/20240920155724/https://www.eecs.harvard.edu/cs286r/courses/fall11/papers/Gibbard73.pdf) and provides nothing more, except for the Rocq code and the illustrative example at the end. It provides a bit less in fact: Gibbard gives a slight generalization considering some possible alternatives which can never be the outcome (even if everyone votes for it). As the point is to find some kind of "good democracy" and as keeping this nuance would consirably complexify the Rocq code, it's here abandoned.


## Gibbard's theorem

Gibbard proved in fact a more general theorem. In the context of an election in which there are at least 3 alternative, it states that if every voter has a vote which defends the best its opinions regardless of the other votes, then one of the voters can decide alone (that is regardless of the other votes) the outcome of the election.

--MATH_START--
Throughout this section, let $I$ the finite set of individuals (voters) of a society, $X$ be the set of outcomes (eligible candidates) and $(S_i)_{i \in I}$ the sets of strategies available to individuals (in the usual terminology of game theory: strategies are the actions, possibly votes, made by individuals).
--MATH_END--

[//]: # Rocq (25-27)

--MATH_START--
$\mathbf{Definition}$\
A strategy profile is an element of $\bigtimes_{i \in I} S_i$.
--MATH_END--

[//]: # Rocq (29-29)

--MATH_START--
$\mathbf{Definition}$\
A game form is a function of $\bigtimes_{i \in I} S_i \rightarrow X$.
--MATH_END--

[//]: # Rocq (31-31)

--MATH_START--
$\mathbf{Definition}$\
Being given ${\vec s}$ a strategy profile, $i$ an individual and $s \in S_i$, ${\vec s}_{i/s}$ is the strategy profile obtained by replacing ${\vec s}_i$ with $s$ in ${\vec s}$.
--MATH_END--

[//]: # Rocq (33-63)

A vote is said dominant when it defends the best its opinions regardless of the other votes.

--MATH_START--
$\mathbf{Definition}$\
Being given an individual $k \in I$ having a (non-strict) preference order $R$ on outcomes and a game form $g$, a strategy $t$ is dominant for $k$ if whatever strategies adopted by everyone else strategy $t$ for $k$ produces an outcome at
least as high in preference ordering as does any other, that is:
$$\forall \vec s \in \bigtimes_{i \in I} S_i \text{ such that } {\vec s}_i = t, g({\vec s}_{k/t}) R g(\vec s)$$
--MATH_END--

[//]: # Rocq (65-69)

--MATH_START--
$\mathbf{Definition}$\
A game form is straightforward if every player has a dominant strategy, whatever its preference order.
--MATH_END--

[//]: # Rocq (71-74)

A voter is said omnipotent if its vote can decide the issue of the election, regardless of the other votes. We deviate from the term "dictator" used by Gibbard in order to stand out from the "dictator" of [Arrow's theorem](https://www.leibnizproject.com/Articles/arrow_theorem.html), which is analog but different.

--MATH_START--
$\mathbf{Definition}$\
An individual is omnipotent for game form $g$ if, for every outcome $x$, there is a
strategy $\vec s(x)$ for k such that $g(\vec s) = x$ whenever ${\vec s}_k = \vec s(x)$. \
A game form $g$ admits an omnipotent player if one of the $k \in I$ is omnipotent for $g$.
--MATH_END--

[//]: # Rocq (76-93)

--MATH_START--
$\mathbf{Definition}$\
If $g$ is a straightforward game form and $i$ an individual, let $\sigma_i$ be a function which gives a dominant strategy for $i$ from its preference. \
For each $\vec P$ giving a preference order for each individual, let $\sigma(\vec P) = (\sigma_i({\vec P}_i))_{i \in I}$. \
Then let $v$ will be the composition of $g$ and $\sigma$, so that $\forall \vec P, v(\vec P) = g(\sigma(\vec P))$.
--MATH_END--

[//]: # Rocq (95-126)

--MATH_START--
$\mathbf{Definition}$\
A chain ordering is an ordering in which no distinct items are indifferent: $P$ is a
chain ordering iff
$$\forall x, y \in X, x I y \Rightarrow x = y$$
Let $Q$ be a chain ordering of $X$. Let $Z \subseteq X$. \
For each individual $i$, we derive a chain ordering $P_i * Z$ of $X$ from the ordering $P_i$ by moving the members of $Z$ to the top, preserving their ordering with respect to each other except in case of ties, and otherwise ordering everything according to $Q$. In other words, for each pair of alternatives $x, y \in X$, \
(3a) If $x \in Z$ and $y \in Z$, then $x (P_i * Z) y$ iff either $x P_i y$ or both $x I_i y$ and $x Q y$. \
(3b) If $x \in Z$ and $y \notin Z$, then $x (P_i * Z) y$. \
(3c) If $x \notin Z$ and $y \notin Z$, then $x (P_i * Z)y$ iff $x Q y$. \
For each $i \in I$ we have defined a two-place relation $P_i * Z$ between members of $X$. \
Let $\vec P * Z = (P_i * Z)_{i \in I}$.
--MATH_END--

[//]: # Rocq (128-433)

--MATH_START--
$\mathbf{Lemma\text{ }(i)}$\
For each $i \in I$, $P_i * Z$ is a chain ordering.

$\mathbf{proof:}$\
Immediate by case analysis. \
■
--MATH_END--

[//]: # Rocq (435-488)

--MATH_START--
$\mathbf{Lemma\text{ }(ii)}$\
If $Y \subseteq Z$, then $(\vec P * Z) * Y = \vec P * Y$.

$\mathbf{proof:}$\
Immediate by case analysis. \
■
--MATH_END--

[//]: # Rocq (490-597)

--MATH_START--
$\mathbf{Lemma\text{ }(iii)}$\
If $g$ is a straightforward game form, suppose $\vec P$ and $\vec {P'}$ agree on $Z$; that is, suppose
$$\forall i \in I, \forall x, y \in X, (x \in Z \text{ and } y \in Z) \Rightarrow (x P_i y \Leftrightarrow x P_i y)$$
Then $\vec P * Z = \vec {P'} * Z$.

$\mathbf{proof:}$\
Immediate by case analysis. \
■
--MATH_END--

[//]: # Rocq (599-666)

--MATH_START--
$\mathbf{Definition}$\
If $g$ is a straightforward game form and $\vec P$ a preference profile, let $f(\vec P)$ be the binary relation:
$$x \neq y \text{ and } x = v(\vec P * \{x, y\})$$
--MATH_END--

[//]: # Rocq (668-730)

--MATH_START--
$\mathbf{Lemma\text{ }(pairwise\text{ }determination)}$\
If $g$ is a straightforward game form, $x, y$ are outcomes of $X$ and $\vec P, \vec {P'}$ are preference profiles, suppose:
$$\forall i \in I, x {\vec P}_i y \Leftrightarrow x {\vec {P'}}_i y$$
$$\forall i \in I, y {\vec P}_i x \Leftrightarrow y {\vec {P'}}_i x$$
Then $x f(\vec P) y \Leftrightarrow x f(\vec {P'}) y$.

$\mathbf{proof:}$\
From lemma (iii), $\vec P * \{x, y\} = \vec {P'} * \{x, y\}$, and hence
$$x = v(\vec P * \{x,y\}) \Leftrightarrow x = v(\vec {P'} * \{x,y\})$$
which is to say $x f(\vec P) y \Leftrightarrow x (\vec {P'}) y$. \
■
--MATH_END--

[//]: # Rocq (732-800)

--MATH_START--
$\mathbf{Definition}$\
Let the individuals of $I$ be numbered from $1$ to $n$  and $\vec {s'}, \vec t$ be strategy profiles. \
The sequence $\vec {s}^0,...,\vec {s}^n$ is obtained by starting with $\vec {s'}$ and at each step $k$ replacing S\vec {s'}_k$ with $\vec {t}_k$. Thus
$$\vec {s}^0=\vec {s'}$$
$$\vec {s}^k=\vec {s}^{k-1}_{k/\vec {t}_k}$$
and in reverse order,
$$\vec {s}^n=\vec t$$
$$\vec {s}^{k-1}=\vec {s}^k_{k/\vec {s'}_k$$
In other words, for each $k$, $\vec {s}^k$ is the strategy n-tuple $(\vec {s}_i^k)_{i \in I}$ such that for each $i$,
$$\text{(5a) }i \le k \Rightarrow \vec {s}_i^k = \vec {t}_i$$
$$\text{(5b) }i \gt k \Rightarrow \vec {s}_i^k = \vec {s'}_i$$
so that
$$\vec {s}^0=(\vec {s'}_1, \vec {s'}_2, \vec {s'}_3, ...,\vec {s'}_n)$$
$$\vec {s}^1=(\vec {t}_1, \vec {s'}_2, \vec {s'}_3, ...,\vec {s'}_n)$$
$$\vec {s}^2=(\vec {t}_1, \vec {t}_2, \vec {s'}_3, ...,\vec {s'}_n)$$
and so forth.
--MATH_END--

[//]: # Rocq (802-824)

--MATH_START--
$\mathbf{Assertion\text{ }1}$\
Let $g$ be a straightforward game form and $\vec s = \sigma(\vec P)$. \
Suppose for strategy $n$-tuple $\vec {s'}$ and alternatives $x$ and $y$, $x \neq y$, and
$$\text{(4a) }\forall i \in I, y P_i x \Rightarrow \vec {s'}_i = \vec {s}_i$$
$$\text{(4b) }\forall i \in I, \neg x \vec {I}_i y$$
$$\text{(4c) }\neg x f(\vec P) y$$
Then $x \neq g(\vec {s'})$.

$\mathbf{proof:}$\
Suppose on the contrary that $x = g(\vec {s'})$. \
We shall show that for some $k$, $\sigma_k(P_k)$ is not $P_k$-dominant for $k$, contrary to what has been stipulated for $\sigma_k$. \
Let $\vec {P}^* = \vec P * \{x, y\}$, and let strategy $n$-tuple $\vec t = \sigma(\vec {P}^*)$. \
Then $\neg x f(\vec P) y$ means $x = y \lor x \neq v(\vec {P}^*)$, and since $x \neq y$ and $v(\vec {P}^*) = g(\sigma(\vec {P}^*)) = g(\vec  t)$, we have $x \neq g(\vec t)$. \
Since $x = g(\vec {s'})$ but $x \neq g(\vec t)$, we have $x = g(\vec {s}^0)$ but $x \neq \vec {s}^n$. Let $k$ be the least such that $g(\vec {s}^k) \neq x$. \
We shall show that either $\vec {t}_k$ is not $\vec {P}^*_k$-dominant for $k$ or $s_k$ is not $P_k$-dominant for $k$. \
Since $t_k = \sigma_k(\vec {P}^*_k)$,and $\vec {s}_k = \sigma_k(P_k)$, in either case
the original characterization of $\sigma$ is violated. \
The supposition that $x = g(\vec {s'})$ is therefore false. Consider two cases, jointly exhaustive. \
Case 1: $g(\vec {s}^k) = y$ and $y P_k x$ \
Then since $g(\vec {s}^{k-1}) = x$, we have $g(\vec {s}^k) P_k g(\vec {s}^{k-1})$, and since $\vec {s}^{k-1}=\vec {s}^k_{k/\vec {s'}_k}$, it is not the case that $g(\vec {s}^k_{k/\vec {s'}_k}) R_k g(\vec {s}_k), and thus $\vec {s'}_k$ is not  $P_k$-dominant for $k$. But since $y P_k x$, by (4a), $\vec {s'}_k = \vec {s}_k$, and $\vec {s}_k$ is not $P_k$-dominant for $k$. But since $\vec {s}_k = \sigma_k(P_k)$, $\vec {s}_k$ is $P_k$-dominant for $k$, and we have a contradiction. \
Case 2: $g(\vec {s}^k) \neq y$ or $x P_k y$ \
Then we always have $x \vec {P}^*_k g(\vec {s}_k)$. For if $g(\vec s_k) = y$, then $x P_k y$, and by (3a) and the definition of $\vec {P}^*$, $x \vec {P}^*_k y$. If, instead, $g(\vec {s}^k) \neq y$, then since $g(\vec {s}^k) \neq x$, we have $g(\vec {s}^k) \notin \{x, y\}$, and by (3b), again $x \vec {P}^*_k g(\vec {s}^k)$. Now $x = g(\vec {s}^{k-1})$, and $\vec {s}^k = \vec {s}^{k-1}_{k/\vec {t}_k}$. Hence $g(\vec {s}^{k-1}) \vec {P}^*_k g(\vec {s}^{k-1}_{k/\vec {t}_k})$, and $\vec {t}_k$ is not ${P}^*_k$-dominant for $k$. But since $\vec {t}_k = \sigma_k(\vec {P}^*_k)$,
$\vec {t}_k$ is ${P}^*_k$-dominant for $k$, and we have a contradiction. \
Since by (4b), $\neg x I_k y$, the two cases exhaust the possibilities.Therefore $x \neq g(\vec {s'})$,and the assertion is proved. \
■
--MATH_END--

[//]: # Rocq (826-1306)

--MATH_START--
$\mathbf{Corollary\text{ }1}$\
Let $g$ be a surjective straightforward game form. If $\forall i \in I, x P_i y$, then $x f(\vec P) y$.

$\mathbf{proof:}$\
Since $x$ is an outcome, for some strategy $n$-tuple $\vec {s'}$, $x = g(\vec {s'})$. \
If $\vec s = \sigma(\vec P)$, then all the hypotheses of Assertion 1 are satisfied except for (4c), and the conclusion of Assertion 1 is violated. \
Therefore (4c) is false, and $x f(\vec P) y$. \
■
--MATH_END--

[//]: # Rocq (1308-1358)

--MATH_START--
$\mathbf{Corollary\text{ }2}$\
If $\forall i \in I, \neg x I_i y$ and $\neg x f(\vec P) y$, then $v(\vec P) \neq x$.

$\mathbf{proof:}$\
(4b). and (4c) in Assertion 1 are satisfied. \
Let $\vec {s'} = \vec s = \sigma(\vec P)$. \
Then in addition, (4a) is satisfied, and by Assertion 1, $g(\vec {s'}) \neq x$. \
Thus since $g(\vec {s'}) = g(\sigma(\vec P)) = v(\vec P)$, we have $v(\vec P) \neq x$. \
■
--MATH_END--

[//]: # Rocq (1360-1389)

--MATH_START--
$\mathbf{Corollary\text{ }3}$\
If $\forall i \in I, \neg x I_i y$ and $v(\vec P) = x$, then $x f(\vec P) y$.

$\mathbf{proof:}$\
This is the contrapositive of Corollary 2. \
■
--MATH_END--

[//]: # Rocq (1391-1406)

--MATH_START--
$\mathbf{Assertion\text{ }2}$\
If $g$ is a surjective straightforward game form and $\vec P$ a preference profile, $f(\vec P)$ is a preference ordering.

$\mathbf{proof:}$\
$f(\vec P)$ clearly satisfies the condition
$$\forall x, y \in X, \neg (x f(\vec P) y \land y f(\vec P) x)$$
for $x f(\vec P) y$ means
$$x \neq y \land x = v(\vec {P'} * \{x,y\})$$
and $y f(\vec P) x$ means
$$x \neq x \land y = v(\vec {P'} * \{x,y\})$$
It remains to show that $f(\vec P)$ satisfies the condition that for all x, y, and z outcomes,
$$x f(\vec P) z \Rightarrow \forall y \in X, x f(\vec P) y \lor y f(\vec P) z$$
Let $\vec {P'} = f(\vec P) * \{x, y, z\}$. Then from (ii), $\vec {P'} * \{x, z\} = f(\vec P) * \{x, z\}$, so that since
$$x f(\vec P) z \Leftrightarrow (x \neq z \land x = v(\vec P * \{x, z\}))$$
and
$$x f(\vec {P'}) z \Leftrightarrow (x \neq z \land x = v(\vec {P'} * \{x, z\}))$$
we have
$$x f(\vec {P'}) z \Leftrightarrow x f(\vec P) z$$
Similarly,
$$x f(\vec {P'}) y \Leftrightarrow x f(\vec P) y$$
and
$$y f(\vec {P'}) z \Leftrightarrow y f(\vec P) z$$
We need only to show, then, that for all x, y, and z outcomes,
$$x f(\vec {P'}) z \Leftrightarrow (x f(\vec {P'}) y \lor y f(\vec {P'}) z$$
Suppose $x f(\vec {P'}) z$. Then $x$ and $z$ are distinct, since $x f(\vec {P'}) z$ means
$$x \neq z \land x = v(\vec {P'} * \{x,z\})$$
If $y = x$, we have $y f(\vec {P'}) z$, and if $y = z$, we have $x f(\vec {P'}) y$. \
There remains the case where $y \neq x$ and $y \neq z$. Then by (i) and the definition of $\vec {P'}$, each $P'_i$ is a chain ordering, and
$$\forall i \in I, (\neg x I'_i y \land \neg x I'_i z \land \neg y I'_i z)$$
Case 1: $x = v(\vec {P'})$ \
Then by Corollary 3 to Assertion 1, $x f(\vec {P'}) y$. \
Case 2: $x \neq v(\vec {P'})$ \
Since $x f(\vec {P'}) z$, by Corollary 2 to Assertion 1, $z \neq v(\vec {P'})$. If $w \notin \{x, y, z\}$, then by (3b) and the definition of $\vec {P'}$, $\forall i \in I, x \vec {P'}_i w$. Hence by Corollary 1 to Assertion 1, $x f(\vec {P'}) w$, and by Corollary 2, $w \neq v(\vec {P'})$. We have, then, $x \neq v(\vec {P'})$, $z \neq v(\vec {P'})$, and if $w \notin \{x, y, z\}$, then $w \neq v(\vec {P'})$. Thus by elimination, $y = v(\vec {P'})$, and by Corollary 3 to Assertion 1, $y f(\vec {P'}) z$. From $x f(\vec {P'}) z$, we have shown that in Case 1, $x f(\vec {P'}) y$, and in Case 2, $y f(\vec {P'}) z$. This, as we said, suffices to show that $f(\vec P)$ is an ordering, and the assertion is proved. \
■
--MATH_END--

[//]: # Rocq (1408-1758)

--MATH_START--
$\mathbf{Assertion\text{ }3}$\
If $g$ is a surjective straightforward game form and has at least three possible outcomes, then $f$ violates the Arrow condition of non-dictatorship (see [the article Arrow's theorem](https://www.leibnizproject.com/Articles/arrow_theorem.html)) for precisions.

$\mathbf{proof:}$\
Since by Assertion 2, the values of $f$ are preference orderings, $f$ is an
Arrow social welfare function. \
We have shown that $f$ satisfies all of the Arrow conditions but non-dictatorship. \
In the first place, since every outcome of $g$ is an outcome of $v$, there are at least 3 alternatives. \
By our previous lemma, $f$ satisfies pairwise determination, and by Corollary 1 to Assertion 1, $f$ satisfies unaminity. \
Therefore, since the Arrow theorem says that no social welfare function satisfies all four Arrow conditions, $f$ violates non-dictatorship. \
■
--MATH_END--

[//]: # Rocq (1760-1821)

--MATH_START--
$\mathbf{Assertion\text{ }4}$\
A dictator for $f$ is omnipotent for $g$.

$\mathbf{proof:}$\
Let $k$ be a dictator for $f$. Then $k$ is omnipotent for $g$ if for every outcome $y$, there is a strategy $s(y)$ for $k$ such that
$$\text{(6) }\forall \vec {s'} \in \bigtimes_{i \in I}, \vec {s'}_k = s(y) \Rightarrow g(\vec {s'}) = y$$
Let $P^y$ be any ordering such that $\forall x \in X, x \neq y \Rightarrow y P^y x$ and let $s(y) = \sigma_k(P^y)$. We appeal to Assertion 1 to show that this s(y) satisfies (6). \
Let $s'$ be such that $s'_k = s(y)$, and suppose $x \neq y$. Then by the way $P^y$ was characterized, $y P^y x$. We shall show that $g(s') \neq x$. Let $\vec P$ be any preference $n$-tuple such that
$$\text{(7a) }P_k = P^y$$
$$\text{(7b) }\forall i \in I, i \neq k \Rightarrow x P_i y$$
and let $s = \sigma(\vec P$). Then $s_k = \sigma_k(P_k) = \sigma_k(P^y) = s(y) = s'_k$. \
Thus since by (7b), only $k$ prefers $y$ to $x$, (4a) is satisfied, and since in addition, $y P^y x$ and hence by (7a) $y P_k x$, (4b) is satisfied also. \
Since $y P_k x$ and $k$ is dictator for $f$, we have $y f(\vec P) x$, and (4c) is satisfied. Therefore by Assertion 1, $x \neq g(s')$. Hence $y = g(s')$. \
We have shown, then, that if $s(y) = \sigma_k(P^y)$, then (6) is satisfied. Thus $k$ is omnipotent for $g$. \
■
--MATH_END--

[//]: # Rocq (1823-1924)

--MATH_START--
$\mathbf{Gibbard's\text{ }theorem}$\
Every surjective straightforward game form with at least three possible outcomes has an omnipotent player.

$\mathbf{proof:}$\
Let $g$ be such a game form. \
By Arrow's theorem together with Assertion 3, $f$ admits a dictator, which is omnipotent for $g$ by assertion 4. \
■
--MATH_END--

[//]: # Rocq (1926-1949)


## Gibbard-Satterthwaite theorem

If there are at least 3 (eligible) alternatives at an election where each voter provides her preference order on candidates (some information may be ignored by the voting scheme: we often consider each voter's top choice only), and if no voter can decide alone alone the outcome, then the election is manipulable (a voter can get a more favorable issue by lying on her preference).

--MATH_START--
Throughout this section, let $I$ the finite set of individuals (voters) of a society and $X$ be the set of alternatives (candidates). \
The strategies are prefence orders on the set of alternatives (for every voter).
--MATH_END--

[//]: # Rocq (1955-1964)

--MATH_START--
$\mathbf{Definition}$\
A voting scheme $v$ is manipulable if for some $k \in I$ and preference orders $\vec P$ and $\vec {P'}$, $P_i = P'_i$ except when $i = k$, and
$$v(\vec {P'}) P_k v(\vec {P})$$
For, then, if $P_k$ is $k$'s real preference ordering, given the way the others vote, $k$ prefers the result of expressing preference ordering $P'_k$ to that of expressing $P_k$.
--MATH_END--

[//]: # Rocq (1966-1971)

--MATH_START--
$\mathbf{Gibbard-Satterthwaite\text{ }theorem}$\
Every voting scheme in which every alternative is eligible and with at least three alternatives has an omnipotent voter or is manipulable.

$\mathbf{proof:}$\
Suppose $v$ has no omnipotent voter and has at least three possible outcomes. \
Then, since $v$ is a game form, $v$ is not straightforward, and thus for some $k$ and $P^*$, no strategy is $P^*$-dominant for $k$. \
In particular, $P^*$ is not $P^*$-dominant for $k$. Hence for some strategy $n$-tuple $\vec P$ of orderings of $X$, it is not the case that $v(\vec {P}_{k/P^*}) R v(\vec P)$, and so $v(\vec P) P v(\vec {P}_{k/P^*})$. \
But since $v(\vec P) \in X$ and $v(\vec {P}_{k/P^*}) \in X$, from (2), $v(\vec P) P^* v(\vec {P}_{k/P^*})$, and $v$ is manipulable. \
■
--MATH_END--

[//]: # Rocq (1973-2013)


## An illustrative example

The Gibbard-Satterthwaite theorem is not very intuitive: if two referendums are planned, the first asking the population what flag should be adopted (chosen between two flags denoted Y and N) and the second one asking if the death penalty should be enforced (the two possible answers being Y for yes and N for no), how could some voters manipulate the election to get a better outcome?

Let's suppose for example that:\
- one-third of the voters (called A) prefer the Y flag and are for the death penalty \
- one-third of the voters (called A) prefer the N flag and are for the death penalty \
- one-third of the voters (called C) prefer the N flag and are against the death penalty \
If everyone is sincere, the N flag will be adopted and the death penalty will be enforced (the outcome is NY). But there are surveys which reveal to the C-voters that the death penalty will very likely be enforced. Then they note that the N flag, despite looking good, is red, which could make the people more violent (based on a recent study). So that, if death penalty is enforced, the C-voters prefer the Y flag: their sincere preference order is NN > YN > YY > NY but they will vote YN and thus get the outcome YY (instead of NY if they had been sincere).
