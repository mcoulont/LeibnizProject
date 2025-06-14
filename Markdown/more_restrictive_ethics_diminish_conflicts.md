---
title: "More restrictive individual ethics diminish the risk of conflicts"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - philosophy
  - ethics
  - society
...


## Presentation

In a society composed of individuals, it is proved here with given definitions that the more individuals have a restrictive in their personnal ethic, the less likely conflicts are.

One relies on [this article](https://leibnizproject.com/Articles/objective_ethics_no_disapproval_iff_same_ethic.html).

--MATH_START--
Throughout this page, let $I$ be the finite set of individuals of a society, $S$ be the set of states, $A$ be the set of actions, $SubjStates = \{(s, i)\}_{s \in S, i \in I}$ be the set of individual states and $E = \{⊤, ⊥\}^{SubjStates \times A}$ the set of ethics.
--MATH_END--

[//]: # Coq (2-9)


## Compared restrictiveness of two ethics

An ethic is more restrictive than another if it allows fewer actions.

--MATH_START--
$\mathbf{Definition}$\
Let $e_1, e_2$ be individual ethics.
$e_1$ is said more restrictive than $e_2$ in state $(s, k)$ if $\forall a \in A, e_1((s, k), a) \implies e_2((s, k), a)$.
--MATH_END--

[//]: # Coq (11-14)

An ethic is strictly more restrictive than another if it allows strictly fewer actions.

--MATH_START--
$\mathbf{Definition}$\
Let $e_1, e_2$ be individual ethics.
$e_1$ is said strictly more restrictive than $e_2$ in state $(s, k)$ if it's more restrictive, $\exists a \in A, e_1((s, k), a) = ⊥$ and $e_2((s, k), a) = ⊤$.
--MATH_END--

[//]: # Coq (16-20)


## Feasability

We introduce the notion of practical fesability. For example, it's not possible that 30 persons simultaneously sit on a public bench.

--MATH_START--
$\mathbf{Definition}$\
Let $feasible$ be a function which at each $s \in S, (a_i) \in A^I$ associates $⊥$ if it's not concretely possible that each individuals $i$ does the $a_i$ action and $⊤$ if it is.

$\mathbf{Definition}$\
$feasible$ is said to involve constraints in $s$ if $\exists (a_i) \in A^I, \neg feasible(s, (a_i))$.
--MATH_END--

[//]: # Coq (22-28)


## Conflicts

A conflict occurs when not every individual (following its own ethic) can do the action (s)he wants.

--MATH_START--
$\mathbf{Definition}$\
Let $s \in S, (e_i) \in E^I, (a_i) \in A^I$.
We say that everyone follows its ethic if $\forall i \in I, e_i((s, i), a_i)$.

$\mathbf{Definition}$\
Let $s \in S, (e_i) \in E^I, (a_i) \in A^I$.
There is a conflict if
$$\begin{cases*}
  \neg feasible(s, (a_i)) \\
  \text{ everyone follows its ethic }
\end{cases*}$$
--MATH_END--

[//]: # Coq (30-42)


## More restrictive individual ethics diminish the risk of conflicts

--MATH_START--
$\mathbf{Definition}$\
Let $s(e_i) \in E^I, e \in E$.
For some $j \in I$, replacing $e_j$ with $e$ in $(e_i)$ results in $(e_i)_{j/e}$.
--MATH_END--

[//]: # Coq (44-46)

If an individual ethic is replaced with a more restrictive one, this can't create a conflict.

--MATH_START--
$\mathbf{Proposition}$\
Let $s \in S, (e_i) \in E^I, (a_i) \in A^I, j \in I, e \in E$.
If $e_j$ is more restrictive than $e$ and $s, (e_i), (a_i)$ conflict, then $s, (e_i)_{j/e}, (a_i)$ conflict.

$\mathbf{proof:}$\
As $s, (e_i), (a_i)$ conflict, we have $\neg feasible(s, (a_i))$ and $\forall i \in I, e_i((s, i), a_i)$ by definition. \
As $e_j$ is more restrictive than $e$, we have $e((s, j), a_j)$. \
We can cconclude that $s, (e_i)_{j/e}, (a_i)$ conflict. \
■
--MATH_END--

[//]: # Coq (48-66)

And if not everything is feasible, one can create a conflict by unrestricting a single individual ethic.

--MATH_START--
$\mathbf{Proposition}$\
Let $j \in I$.
If $feasible$ involves constraints, then $\exists s \in S, (e_i) \in E^I, (a_i) \in A^I, e \in E,$ such that
$$\begin{cases*}
  e_j \text{ is more restrictive than } e \text{ in subjective state } (s, j) \\
  (e_i), (a_i) \text{ don't conflict in } s \\
  (e_i)_{j/e}, (a_i) \text{ conflict in } s
\end{cases*}$$

$\mathbf{proof:}$\
Let $s \in S, (a_i) \in A^I$ unfeasible. \
Let $(e_i) \in E^I$ defined in $s$ by (whatever state and action)
$$\begin{cases*}
  ⊥ \text{ if } i = j \\
  ⊤ \text{ otherwise }
\end{cases*}$$
Then, as $j$ doesn't act accordingly to its ethic, $(e_i), (a_i)$ don't conflict in $s$. \
Let $e \in E$ defined by $e((s, i), a) = ⊤ \text{ } \forall (s, i) \in SubjStates, a \in A$. \
Then, as $e$ allows everything, $e_j$ is more restrictive than $e$. \
Now, $(e_i)_{j/e}((s, i), a) = ⊤ \text{ } \forall (s, i) \in SubjStates, a \in A$, which creates a conflict together with the fact that $s, (a_i)$ is not feasible. \
■
--MATH_END--

[//]: # Coq (68-101)
