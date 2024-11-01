# tlaplus-journey
TLA+ algorithms with TLAPS proofs

# [MoneyTransfer](src/moneyTransfer/MoneyTransfer.tla)
A simple (but not trivial) algorithm modeling money transfer between accounts.

What makes the algorithm non-trivial:
1. It is **fault-tolerant**.
2. It models any number of accounts and money transfers.
3. It is [fully proved](src/moneyTransfer/MoneyTransfer_proofs.tla) using The TLA+ Proof System (TLAPS).
4. The main invariant that is proved is a **global invariant**: the global amount of money present in the model.

# Pre-Requisites
The project is being developed using:
- [TLA+ Toolbox v1.7.4](https://github.com/tlaplus/tlaplus/releases/tag/v1.7.4)
- [TLA+ Proof manager (tlapm)](https://github.com/tlaplus/tlapm)
- [TLA+ Community Modules](https://github.com/tlaplus/CommunityModules)

tlapm needs to be **built from sources**. The [latest available](https://github.com/tlaplus/tlapm/commit/ffb8846ff3c49d53ee6eeedfc4c8c4c409306ae3) sources of tlapm are used. The reason to build tlapm from sources is that its released versions use outdated [Isabelle](https://isabelle.in.tum.de) versions. And outdated Isabelle fails to prove some theorems. Using released versions of tlapm is possible but some theorems will not be proved.

The [latest tagged version](https://github.com/tlaplus/CommunityModules/releases/tag/202409181925) of Community Modules is used. The Community Modules source code is just checked out and the sources are directly used.

# Running the specification

## Running via IntelliJ

You can run the [MoneyTransfer](src/moneyTransfer/MoneyTransfer.tla) specification with IntelliJ, and it requires the TLA+ plug-in.

You have to specify the location of tlapm modules and Community Modules to run the specification:
> -DTLA-Library=/usr/local/lib/tlaps:`<Community Modules source parent directory>`/CommunityModules/modules