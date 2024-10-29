---- MODULE MC ----
EXTENDS MoneyTransfer, TLC

\* CONSTANT definitions @modelParameterConstants:0NAccount
const_1730232188438153000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:1NTransfer
const_1730232188438154000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:2Empty
const_1730232188438155000 == 
0
----

\* CONSTANT definitions @modelParameterConstants:3NAvail
const_1730232188438156000 == 
1
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_1730232188438157000 ==
0..3
----
\* CONSTRAINT definition @modelParameterContraint:0
constr_1730232188438158000 ==
LimitedIndInv
----
=============================================================================
\* Modification History
\* Created Tue Oct 29 21:03:08 CET 2024 by pawelsidoryk
