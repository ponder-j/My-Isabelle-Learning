结构归纳法
![[Pasted image 20251109100350.png]]


数学归纳法
![[Pasted image 20251109100408.png]]


规则归纳法
![[Pasted image 20251109100424.png]]
Isabelle 会根据定义的递归函数自动生成 fun.induct 规则，用于后续的推理证明，用法如下：
```isabelle
proof (induct x rule: fun.induct)
```
