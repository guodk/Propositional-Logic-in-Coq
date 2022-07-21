# Propositional-Logic-in-Coq
建立命题逻辑演绎系统
证明完全性定理（包括公式集和自然数集存在双射）
给出命题逻辑下永真式（或内定理）的自动化证明策略
其中

base_pc.v 定义了Formula

syntax.v 定义了命题逻辑演绎系统L的语法，证明了一些L的定理

semantec.v 定义了命题逻辑系统的语义，给出了一个对所有永真式实现自动化证明的Ltac

classical_logic_axiom_system_equivalence.v 定义了另外三种命题逻辑系统，并证明它们与L等价

Mappings.v参考了https://github.com/QinxiangCao/Countable_PaperSubmission ，这部分的目的是为了证明存在Formula->nat的单射

bijection_nat_Formula.v 证明了Bernstein定理，从而证明了存在nat->Formula的双射

complete.v 证明了可靠性定理、完全性定理，给出一个对所有内定理实现自动化证明的Ltac

auto_examples.v 举例试试自动化证明策略的效果
