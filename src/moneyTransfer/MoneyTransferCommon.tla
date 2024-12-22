---- MODULE MoneyTransferCommon ----
EXTENDS Naturals

CONSTANTS Empty, Account, Transfer, Avail

NNat == Nat \ {0}

EAccount == Account \cup {Empty}

====
