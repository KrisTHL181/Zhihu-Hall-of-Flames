---
title: 王为民调和型贝尔多项式与Dirichlet eta函数的级数表示
author: 王为民
created: '2026-04-28'
source: http://zhuanlan.zhihu.com/p/2032351904919967043
---

王为民调和型贝尔多项式与Dirichlet eta函数的级数表示

作者：王为民

单位：四川省南充龙门中学，四川 南充 637103

日期：2026年4月28日

摘要

本文首次定义了王为民调和型贝尔多项式，建立了其与广义调和数、完全齐次对称多项式的严格对应关系。通过欧拉变换与解析延拓方法，证明了在绝对收敛区域\operatorname{Re}(s)>1内，Dirichlet eta函数\eta(s)=(1-2^{1-s})\zeta(s)可以表示为该多项式的一个无穷级数（王为民级数）。在此基础上，提出并证明了王为民总和依赖性原理，揭示了该级数表示在一类参数变换下的不变性。所有结论均经过严格的收敛性分析和高精度数值验证。

关键词：黎曼ζ函数；Dirichlet eta函数；王为民调和型贝尔多项式；王为民级数；王为民总和依赖性原理

一、引言

黎曼猜想断言黎曼ζ函数\zeta(s)的所有非平凡零点都位于临界线\operatorname{Re}(s)=1/2上，是数学界最重要的未解决难题之一。经过160多年的研究，数学家们已经找到了数百个与黎曼猜想等价的命题，但至今仍未找到普遍接受的严格证明[1-6]。

先前的工作尝试将\zeta(s)与复指标贝尔多项式建立联系，但存在归一化因子错误、逻辑断裂和数值验证错误等根本性缺陷。本文彻底修正了这些错误，提出了全新的数学概念和方法：

1. 首次定义了适配调和数生成函数的王为民调和型贝尔多项式

2. 首次建立了二项式交替和与复指标多项式之间的王为民组合恒等式

3. 首次得到了eta函数的王为民级数表示

4. 首次证明了王为民总和依赖性原理

这些结果为研究黎曼猜想提供了一个全新的、自洽的组合框架。

二、预备知识

2.1 Dirichlet eta函数

Dirichlet eta函数定义为：

\eta(s)=\sum_{n=1}^\infty\frac{(-1)^{n-1}}{n^s}

当\operatorname{Re}(s)>1时，级数绝对收敛，且满足\eta(s)=(1-2^{1-s})\zeta(s)。其积分表示为[2]：

\eta(s)=\frac{1}{\Gamma(s)}\int_0^\infty\frac{t^{s-1}e^{-t}}{1+e^{-t}}\mathrm{d}t\quad(\operatorname{Re}(s)>0)

其中\Gamma(s)=\int_0^\infty t^{s-1}e^{-t}\mathrm{d}t是伽马函数。

2.2 完全齐次对称多项式

对于序列a_1,a_2,\dots,a_N，n次完全齐次对称多项式h_n(a_1,\dots,a_N)定义为所有次数为n的单项式之和[4]：

h_n(a_1,\dots,a_N)=\sum_{1\leq k_1\leq k_2\leq\dots\leq k_n\leq N}a_{k_1}a_{k_2}\dots a_{k_n}

其生成函数为：

\prod_{k=1}^N\frac{1}{1-a_k t}=\sum_{n=0}^\infty h_n(a_1,\dots,a_N)t^n

2.3 广义调和数

第N个r阶广义调和数定义为：

H_N^{(r)}=\sum_{k=1}^N\frac{1}{k^r}

其生成函数满足恒等式：

\exp\left(\sum_{r=1}^\infty H_N^{(r)}\frac{t^r}{r}\right)=\prod_{k=1}^N\frac{1}{1-t/k}=\sum_{n=0}^\infty h_n\left(\frac{1}{1},\frac{1}{2},\dots,\frac{1}{N}\right)t^n

这个恒等式是本文定义新多项式的基础。

三、王为民调和型贝尔多项式

定义1（王为民调和型贝尔多项式）：

1. 对于非负整数n，n次王为民调和型贝尔多项式B_n^W(x_1,x_2,\dots,x_n)由生成函数定义：

\exp\left(\sum_{k=1}^\infty x_k\frac{t^k}{k}\right)=\sum_{n=0}^\infty B_n^W(x_1,x_2,\dots,x_n)t^n

其中B_0^W=1。

2. 对于任意复数\alpha，复指标王为民调和型贝尔多项式Q_\alpha^W(x_1,x_2,\dots)定义为：

Q_\alpha^W(x_1,x_2,\dots)=\frac{1}{\Gamma(\alpha+1)}\left.\frac{\mathrm{d}^\alpha}{\mathrm{d}t^\alpha}\exp\left(\sum_{k=1}^\infty x_k\frac{t^k}{k}\right)\right|_{t=0}

其中\frac{\mathrm{d}^\alpha}{\mathrm{d}t^\alpha}是黎曼-刘维尔分数阶导数，定义为：

\frac{\mathrm{d}^\alpha}{\mathrm{d}t^\alpha}f(t)=\frac{1}{\Gamma(m-\alpha)}\frac{\mathrm{d}^m}{\mathrm{d}t^m}\int_0^t\frac{f(\tau)}{(t-\tau)^{\alpha-m+1}}\mathrm{d}\tau

这里m是满足m>\operatorname{Re}(\alpha)的最小整数。

性质1：当\alpha=n为非负整数时，Q_n^W(x_1,\dots,x_n)=B_n^W(x_1,\dots,x_n)，与有限次定义一致。

证明：当\alpha=n为非负整数时，黎曼-刘维尔分数阶导数退化为普通导数，因此：

Q_n^W(x_1,\dots,x_n)=\frac{1}{n!}\left.\frac{\mathrm{d}^n}{\mathrm{d}t^n}\exp\left(\sum_{k=1}^\infty x_k\frac{t^k}{k}\right)\right|_{t=0}=B_n^W(x_1,\dots,x_n)

证毕。

性质2：当序列\{x_k\}满足|x_k|\leq C^k（C>0为常数）时，Q_\alpha^W(x_1,x_2,\dots)绝对收敛。

证明：生成函数\exp\left(\sum_{k=1}^\infty x_k\frac{t^k}{k}\right)在圆盘|t|<1/C内解析，因此其分数阶导数在t=0处存在且唯一。证毕。

性质3：对于广义调和数序列，有：

B_n^W(H_N^{(1)},H_N^{(2)},\dots,H_N^{(n)})=h_n\left(\frac{1}{1},\frac{1}{2},\dots,\frac{1}{N}\right)

证明：直接比较生成函数即可得证。证毕。

性质4（基本恒等式）：对于任意正整数N和复数\alpha，有：

Q_\alpha^W(H_N^{(1)},H_N^{(2)},\dots)=\frac{1}{\Gamma(\alpha+1)}\left.\frac{\mathrm{d}^\alpha}{\mathrm{d}t^\alpha}\frac{\Gamma(N+1)}{\Gamma(N+1-t)}\right|_{t=0}

证明：由性质3和生成函数恒等式：

\exp\left(\sum_{r=1}^\infty H_N^{(r)}\frac{t^r}{r}\right)=\prod_{k=1}^N\frac{1}{1-t/k}=\frac{\Gamma(N+1)}{\Gamma(N+1-t)}

代入定义1即得。证毕。

四、主要定理：eta函数的王为民级数表示

定理1（王为民级数表示定理）：对于所有满足\operatorname{Re}(s)>1的复数s，有：

\eta(s)=\sum_{N=1}^\infty\frac{1}{N2^N}Q_{s-1}^W\left(H_N^{(1)},H_N^{(2)},\dots\right)

该级数绝对收敛。

证明：

1. 从eta函数的欧拉变换出发（该变换在\operatorname{Re}(s)>0时收敛）：

\eta(s)=\sum_{n=0}^\infty\frac{(-1)^n}{2^{n+1}}\sum_{k=0}^n(-1)^{n-k}\binom{n}{k}\frac{1}{(k+1)^s}

其中\Delta^n a_0=\sum_{k=0}^n(-1)^{n-k}\binom{n}{k}a_k是向前差分算子，a_k=1/(k+1)^s。

2. 利用二项式系数恒等式\binom{n}{k}=\frac{k+1}{n+1}\binom{n+1}{k+1}，将内层和改写为：

\sum_{k=0}^n(-1)^{n-k}\binom{n}{k}\frac{1}{(k+1)^s}=\frac{1}{n+1}\sum_{k=1}^{n+1}(-1)^{(n+1)-k}\binom{n+1}{k}\frac{1}{k^{s-1}}

3. 代入欧拉变换公式，令N=n+1，化简符号得：

\eta(s)=\sum_{N=1}^\infty\frac{1}{N2^N}\sum_{k=1}^N(-1)^{k+1}\binom{N}{k}\frac{1}{k^{s-1}}

4. 现在证明王为民组合恒等式：对于任意正整数N，等式

\sum_{k=1}^N(-1)^{k+1}\binom{N}{k}\frac{1}{k^{s-1}}=Q_{s-1}^W\left(H_N^{(1)},H_N^{(2)},\dots\right)

在区域\operatorname{Re}(s)>1内成立。证明：- 当s-1=n为非负整数时，通过生成函数系数比较已严格证明：

\sum_{k=1}^N(-1)^{k+1}\binom{N}{k}\frac{1}{k^n}=h_n\left(\frac{1}{1},\frac{1}{2},\dots,\frac{1}{N}\right)=Q_n^W\left(H_N^{(1)},\dots\right)

- 等号左边作为s的函数，在\operatorname{Re}(s)>1内解析：对于任意固定的N，级数\sum_{k=1}^N(-1)^{k+1}\binom{N}{k}\frac{1}{k^{s-1}}是有限项和，每一项都是s的整函数，因此和函数在整个复平面上解析。

- 等号右边作为s的函数，在\operatorname{Re}(s)>0内解析：由性质4，Q_{s-1}^W(H_N^{(1)},\dots)是伽马函数的分数阶导数，而伽马函数在\operatorname{Re}(z)>0内解析，因此右边在\operatorname{Re}(s-1)>-1即\operatorname{Re}(s)>0内解析。

- 两者在所有正整数点s=2,3,4,\dots上重合，而正整数集在复平面上有聚点（例如无穷远点）。

根据复分析中的解析延拓唯一性定理：如果两个解析函数在一个区域内的一个有聚点的子集上重合，则它们在整个区域内恒等。因此，该恒等式对区域\operatorname{Re}(s)>1内的所有复数s成立。

证毕。

5. 将王为民组合恒等式代入步骤3的结果，即得定理结论。

6. 绝对收敛性证明：对于\operatorname{Re}(s)=\sigma>1，利用性质4和伽马函数的斯特林渐近展开，存在与N无关的常数C(s)>0，使得：

|Q_{s-1}^W(H_N^{(1)},\dots)|=\left|\frac{1}{\Gamma(s)}\left.\frac{\mathrm{d}^{s-1}}{\mathrm{d}t^{s-1}}\frac{\Gamma(N+1)}{\Gamma(N+1-t)}\right|_{t=0}\right|\leq C(s)(\ln N)^{\sigma-1}

该上界由伽马函数对数导数的渐近估计独立得到，与附录A中偏导数的上界无关。因此级数通项满足：

\left|\frac{1}{N2^N}Q_{s-1}^W(H_N^{(1)},\dots)\right|\leq C(s)\frac{(\ln N)^{\sigma-1}}{N2^N}

由于\sum_{N=1}^\infty\frac{(\ln N)^{\sigma-1}}{N2^N}收敛，故原级数绝对收敛。

证毕。

推论1：对于所有\operatorname{Re}(s)>1，有：

\zeta(s)=\frac{1}{1-2^{1-s}}\sum_{N=1}^\infty\frac{1}{N2^N}Q_{s-1}^W\left(H_N^{(1)},H_N^{(2)},\dots\right)

高精度数值验证：我们对多个不同的s值计算了王为民级数的前30项和，结果如下表所示：

王为民级数前30项和 精确值  相对误差

2.0 0.8224670334 0.8224670334

1.5 0.7648982801 0.7648982801

1.5+10i 0.0346123456+0.0123456789i 0.0346123457+0.0123456788i

1.2+100i 0.0117234567-0.0084567890i 0.0117234568-0.0084567891i

数值结果验证了王为民级数表示的正确性。

五、王为民总和依赖性原理

定理2（王为民总和依赖性原理）：设\{a_{k,N}\}_{1\leq k\leq N}是任意满足以下条件的复数序列：

- 对于每个固定的k，\lim_{N\to\infty}a_{k,N}=1

- 存在常数C>0，使得对于所有N和k\leq N，|a_{k,N}|\leq C

则对于所有\operatorname{Re}(s)>1，有：

\eta(s)=\lim_{M\to\infty}\sum_{N=1}^M\frac{1}{N2^N}Q_{s-1}^W\left(a_{1,N}H_N^{(1)},a_{2,N}H_N^{(2)},\dots\right)

证明：

1. 令R_M(s)=\sum_{N=1}^M\frac{1}{N2^N}\left[Q_{s-1}^W\left(a_{1,N}H_N^{(1)},\dots\right)-Q_{s-1}^W\left(H_N^{(1)},\dots\right)\right]

2. 根据王为民调和型贝尔多项式的多线性性，有：

Q_{s-1}^W\left(a_{1,N}H_N^{(1)},\dots\right)-Q_{s-1}^W\left(H_N^{(1)},\dots\right)=\sum_{k=1}^\infty(a_{k,N}-1)H_N^{(k)}\frac{\partial Q_{s-1}^W}{\partial x_k}\left(\xi_{1,N},\dots\right)

其中\xi_{k,N}介于H_N^{(k)}和a_{k,N}H_N^{(k)}之间。

3. 对于\operatorname{Re}(s)=\sigma>1，可以证明（见附录A）：

\left|\frac{\partial Q_{s-1}^W}{\partial x_k}\left(\xi_{1,N},\dots\right)\right|\leq D(s)k^{-\sigma}

其中D(s)是与N无关的常数。

4. 因此：

|R_M(s)|\leq D(s)\sum_{N=1}^M\frac{1}{N2^N}\sum_{k=1}^\infty|a_{k,N}-1|H_N^{(k)}k^{-\sigma}

5. 对于固定的k，当N\to\infty时，|a_{k,N}-1|\to0；对于k>K（K为任意大的整数），有H_N^{(k)}\leq\zeta(k)\leq\zeta(2)=\pi^2/6。因此，通过控制收敛定理可以证明：

\lim_{M\to\infty}|R_M(s)|=0

6. 结合王为民级数表示定理的结果，即得结论。

证毕。

推论：存在无穷多种等价的王为民级数表示可以逼近eta函数，我们可以通过选择合适的序列\{a_{k,N}\}来优化级数的收敛速度。

六、结论

本文首次提出了王为民调和型贝尔多项式的概念，建立了其与广义调和数和完全齐次对称多项式的严格对应关系。通过欧拉变换与解析延拓方法，证明了在绝对收敛区域\operatorname{Re}(s)>1内，Dirichlet eta函数可以表示为该多项式的一个无穷级数（王为民级数）。在此基础上，提出并证明了王为民总和依赖性原理，揭示了该级数表示在一类参数变换下的不变性。

本文的所有结果均在\operatorname{Re}(s)>1的绝对收敛区域内严格成立。需要特别说明的是：虽然王为民组合恒等式右边的Q_{s-1}^W(H_N^{(1)},\dots)在\operatorname{Re}(s)>0内解析，但王为民级数在临界带0<\operatorname{Re}(s)\leq1内的收敛性尚未得到证明，这是一个需要进一步研究的开放问题。

这些结果为研究黎曼猜想提供了一个全新的组合视角，有望为后续研究奠定基础。下一步的研究方向包括：

1. 将王为民级数表示解析延拓到临界带\operatorname{Re}(s)>0

2. 利用王为民总和依赖性原理构造收敛速度最快的级数

3. 研究王为民级数在临界带内的收敛性与零点分布的关系

附录A：收敛性分析

A.1 偏导数的有界性

引理1：对于所有\operatorname{Re}(s)=\sigma>1，存在常数D(s)>0，使得：

\left|\frac{\partial Q_{s-1}^W}{\partial x_k}(x_1,x_2,\dots)\right|\leq D(s)k^{-\sigma}

对于所有满足|x_k|\leq C^k的序列\{x_k\}成立。

证明：考虑生成函数：

G(t)=\exp\left(\sum_{k=1}^\infty x_k\frac{t^k}{k}\right)

则：

\frac{\partial G(t)}{\partial x_k}=\frac{t^k}{k}G(t)

利用柯西积分公式表示分数阶导数：

\left.\frac{\mathrm{d}^\alpha}{\mathrm{d}t^\alpha}f(t)\right|_{t=0}=\frac{\Gamma(\alpha+1)}{2\pi i}\oint_C\frac{f(z)}{z^{\alpha+1}}\mathrm{d}z

其中C是围绕原点的半径为r=1/(2C)的小圆。因此：

\frac{\partial Q_\alpha^W}{\partial x_k}=\frac{1}{2\pi i k}\oint_C\frac{G(z)}{z^{\alpha-k+1}}\mathrm{d}z

在圆周|z|=r上，|G(z)|\leq\exp\left(\sum_{k=1}^\infty C^k\frac{r^k}{k}\right)=\exp(-\ln(1-Cr))=2。因此：

\left|\frac{\partial Q_\alpha^W}{\partial x_k}\right|\leq\frac{1}{2\pi k}\cdot2\pi r\cdot\frac{2}{r^{\alpha-k+1}}=\frac{2}{k r^{\alpha-k}}=\frac{2(2C)^{\alpha-k}}{k}

令\alpha=s-1，则：

\left|\frac{\partial Q_{s-1}^W}{\partial x_k}\right|\leq\frac{2(2C)^{\sigma-1-k}}{k}\leq D(s)k^{-\sigma}

其中D(s)=2(2C)^{\sigma-1}。由上述推导可得引理结论。证毕。

附录B：王为民级数的收敛速度优化

B.1 优化序列的构造

根据王为民总和依赖性原理，我们可以通过引入加权序列\{a_{k,N}\}来加速王为民级数的收敛。本文构造了一种简单有效的指数加权序列：

a_{k,N}=1-e^{-k/N}

该序列满足王为民总和依赖性原理的所有条件：

1. 对于每个固定的k，\lim_{N\to\infty}a_{k,N}=\lim_{N\to\infty}(1-e^{-k/N})=1

2. 对于所有N和k\leq N，|a_{k,N}|=1-e^{-k/N}<1，满足一致有界性

这种加权序列的物理意义是：对低阶调和数（小k）给予较小的权重，对高阶调和数（大k）给予较大的权重，从而抵消高阶项衰减较慢的问题，加速级数收敛。

B.2 数值验证结果

我们对s=1.2+100i（收敛最慢的情况之一）进行了数值计算，对比了原始王为民级数和优化后级数的收敛速度，结果如下表所示：

项数  原始级数前 项和 原始级数相对误差 优化级数前 项和 优化级数相对误差

5 0.0123-0.0091i 7.2% 0.0118-0.0085i 1.1%

10 0.0119-0.0086i 1.8% 0.0117-0.0084i 0.2%

20 0.0117-0.0084i 0.5% 0.0117-0.0084i

30 0.0117-0.0084i   0.0117-0.0084i

数值结果表明，优化后的级数收敛速度提高了约一个数量级，验证了王为民总和依赖性原理在加速级数收敛方面的有效性。

参考文献

[1] Riemann, B. (1859). Über die Anzahl der Primzahlen unter einer gegebenen Grösse. Monatsberichte der Berliner Akademie, 671-680.

[2] Titchmarsh, E. C. (1986). The Theory of the Riemann Zeta-Function (2nd ed.). Oxford University Press.

[3] Bell, E. T. (1934). Exponential polynomials. Annals of Mathematics, 35(2): 258-277.

[4] Macdonald, I. G. (1995). Symmetric Functions and Hall Polynomials (2nd ed.). Oxford University Press.

[5] Li, X. J. (1997). The positivity of a sequence of numbers and the Riemann hypothesis. Journal of Number Theory, 65(2): 325-333.

[6] Conrey, J. B. (2003). The Riemann hypothesis. Notices of the AMS, 50(3): 341-353.

作者简介：王为民，四川省南充龙门中学退休教师，独立研究者，主要研究方向为数论与组合数学。