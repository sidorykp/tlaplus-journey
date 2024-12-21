---- MODULE MoneyTransfer_proofsCommon ----
EXTENDS MoneyTransferCommon

CONSTANTS NAccount, NTransfer

ASSUME AccountAssumption == Account = 1..NAccount

ASSUME TransferAssumption == Transfer = 1..NTransfer

ASSUME NTransferAssumption == NTransfer \in NNat

ASSUME NAccountAssumption == NAccount \in NNat

ASSUME AvailAssumption == Avail \in NNat

ASSUME EmptyAssumption == Empty = 0
====
