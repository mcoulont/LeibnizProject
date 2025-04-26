---
title: 'Altruism is not enough to avoid conflicts'
author: Marc Coulont-Robert
lang: "en"
keywords:
  - philosophy
  - ethics
  - society
...


## Presentation

In a society composed of at least two individuals, it is proved here with given definitions that even if every individual is altruist, conflicts still happen.

One relies on [this article](https://leibnizproject.com/Articles/more_resrtictive_ethics_diminish_conflicts.html).

--MATH_START--
Throughout this page, let $I$ be the finite set of individuals of a society containing at least two of them, $S$ be the set of states, $A$ be the set of actions, $SubjStates = S × I$ be the set of individual states and $E = \{⊤, ⊥\}^{SubjStates \times A}$ the set of ethics. $feasible: S × A^I -> \{⊤, ⊥\}$ is the function of practical feasibility.
--MATH_END--

[//]: # Coq (2-15)


## Altruism

We define altruism of an individual $i$ as the fact that if everyone did like $i$, there would be no conflict. This is not the usual definition of altruism. If you have a better name for this concept, [propose it in Github](https://github.com/mcoulont/LeibnizProject/issues/new).

--MATH_START--
$\mathbf{Definition}$\
Generalizing an individual ethic $e$ to the whole society is the fact to consider that every individual has ethic $e$.

$\mathbf{Definition}$\
An ethic $e$ is said altruist in $s$ if $\exists (a_i) \in A^I$ such that there is no conflict if $e$ is generalized to the whole society.
--MATH_END--

[//]: # Coq (17-21)


## Bipartite contest

A bipartite contest is a situation where two individuals can do two conflictual actions (regardless of how act the other individuals) but things can work out if one of them gives up his action. For example, two individuals may want to seat on a chair in a public garden; this creates a conflict, unless one of them lets the chair to the other one.

--MATH_START--
$\mathbf{Definition}$\
Let $s$ be a state and $i \neq j$ two individuals.
There's a bipartite contest between $i$ and $j$ over actions $a_i, a_j$ with possible renunciations $b_i, b_j$ if
$$\begin{cases*}
  \forall (ap_k) \in A^I \text{ such that } ap_i = a_i \text{ and } ap_j = a_j \text{, we have } \neg feasible(s, (ap_k)) \\
  \exists (ap_k) \in A^I \text{ such that } ap_i = a_i, ap_j = b_j \text{ and } feasible(s, (ap_k)) \quad \text{(case $j$ gives up)} \\
  \exists (ap_k) \in A^I \text{ such that } ap_i = b_i, ap_j = a_j \text{ and } feasible(s, (ap_k)) \quad \text{(case $i$ gives up)}
\end{cases*}$$
--MATH_END--

[//]: # Coq (23-41)


## Unanimous altruism is not enough to avoid conflicts

In our example of bipartite contest, the first individual may think something like "the oldest should be given the seat" and the second one something like "first come first served". Both opinions permit to avoid conflicts if everyone shares them, but there is still a conflict if the first individual is older than the second one.

--MATH_START--
$\mathbf{Proposition}$\
In a state $s$, if there a bipartite contest between individuals $i$ and $j$ over actions $a_i, a_j$ with possible renunciations $b_i, b_j$, then there exists $(e_k) \in E^I, (ap_k) \in A^I$ such that
$$\begin{cases*}
  \forall k \in I,e_k \text{ is altruist} \\
  \text{ there is a conflict }
\end{cases*}$$

$\mathbf{proof:}$\
Let $(e_k) \in E^I$ defined by
$$\begin{cases*}
  e_i((s, i), a_i) = ⊤, e_i((s, i), b_i) = ⊤ \text { and } e_i((s, i), a) = ⊥ \text{ for all other actions } a \\
  e_i((s, j), b_j) = ⊤ \text { and } e_i((s, j), a) = ⊥ \text{ for all other actions } a \\
  e_i((s, k), a) = ⊤ \text{ for other } k \text{'s and all actions } a \\
  \text{ if } k \neq i, \\
  e_k((s, j), a_j) = ⊤, e_k((s, j), b_j) = ⊤ \text { and } e_k((s, j), a) = ⊥ \text{ for all other actions } a \\
  e_k((s, i), b_i) = ⊤ \text { and } e_k((s, i), a) = ⊥ \text{ for all other actions } a \\
  e_k((s, l), a) = ⊤ \text{ for other } l \text{'s and all actions } a
\end{cases*}$$
Let $(ap_k) \in A^I$ defined by
$$\begin{cases*}
  ap_i = a_i \\
  ap_k = a_j \text{ for other } k \text{'s}
\end{cases*}$$
- Let's prove firstly that there is a conflict. The unfeasability comes from the definitions of $(ap_k)$ and bipartite conflict (the first of the three assertions). The fact that everyone follows its ethic flows directly from the definitions of $(e_k)$ and $(ap_k)$. \
- Let's now conclude by proving that every individual is altruist. \
  $\quad$ For individual $i$, the following action profile $(api_k)$ permits to avoid a conflict:
    $$\begin{cases*}
      api_i = a_i \\
      api_j = b_j \\
      api_k \text{ is given by the definition of bipartite contest (the second of the three assertions) }
    \end{cases*}$$
  $\quad$ For other individuals, the following action profile $(apl_k)$ permits to avoid a conflict:
    $$\begin{cases*}
      api_i = b_i \\
      api_j = a_j \\
      api_k \text{ is given by the definition of bipartite contest (the third of the three assertions) }
    \end{cases*}$$
■
--MATH_END--

[//]: # Coq (43-262)
