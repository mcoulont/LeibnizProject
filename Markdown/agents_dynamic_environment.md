---
title: "Agents in dynamic environments"
author: Marc Coulont-Robert
lang: "en"
keywords:
  - agent_based_model
...


## Presentation

Until now, time was not taken into account: we were in a given state at a certain instant and had a range of actions at our disposal, to do now. The model was thus static and couldn't express long-term projects. For example, you may want to get a degree, but this is not just about a single action at a certain instant, but all a set of actions done at different moments.

Here individuals are named agents according to a classical terminology in (pre-machine learning) artificial intelligence.

--MATH_START--
Throughout this page, let $T$ be the set of instants in the unfolding of time. If $t, t' \in T$, $t \le t'$ means that the instant $t$ is before (or simultaneous with) $t'$. \
Let $S$ be the set of states, $A$ the set of actions and $Ag$ the set of agents.
--MATH_END--

[//]: # Coq (7-11)


## Foundational definitions

A history is all what happened through time (successive states and actions done by every agent). A history until a certain instant is all what happened through time until this instant. A history extends a history until a certain instant if both coincide before (and at) that instant.

--MATH_START--
$\mathbf{Definition}$\
$H = T \rightarrow S \times A^{Ag}$. \
$H_{t_0} = \{t \in T | t \le t_0\} \rightarrow S \times A^{Ag}$ (where $t_0 \in T$).

$\mathbf{Definition}$\
Let $t_0 \in T$, $h \in H$ and ${hu} \in H_{t_0}$. \
$h$ is said to extend ${hu}$ if $\forall t \le t_0, h(t) = {hu}(t)$.
--MATH_END--

[//]: # Coq (13-22)
