---
title: 'Ethics: first steps'
author: Marc Coulont-Robert
lang: "en"
keywords:
  - philosophy
  - ethics
...


## Presentation

An ethic is the rule of conduct which tells in each given situation if an action is ethical.


## Definition of an ethic

Being given a situation (also named state following the usual terminology in artificial intelligence: see [this Wikipedia page](https://en.wikipedia.org/wiki/Intelligent_agent#Objective_function) for example), an ethic tells if the action is right or wrong in the situation.

--MATH_START--
Throughout this page, let $S$ be the set of states and $A$ the set of actions.

$\mathbf{Definition}$\
An ethic is a function from $S × A$ to $\{⊥ ,⊤\}$, where $⊥$ is the image for actions being unethical and $⊤$ the one for ethical actions.
--MATH_END--

[//]: # (2-9)
