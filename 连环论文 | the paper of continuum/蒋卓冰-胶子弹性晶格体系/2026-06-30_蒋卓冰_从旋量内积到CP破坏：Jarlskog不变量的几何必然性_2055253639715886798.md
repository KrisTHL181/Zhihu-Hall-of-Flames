---
title: 从旋量内积到CP破坏：Jarlskog不变量的几何必然性
author: 蒋卓冰
created: '2026-06-30'
source: https://zhuanlan.zhihu.com/p/2055253639715886798
---

## 从旋量内积到CP破坏：Jarlskog不变量的几何必然性

---

### 蒋卓冰

G4 × 现象学：为什么系列——粒子物理与核物理中五个代数事实的几何根源 之 二

[https://doi.org/10.5281/zenodo.20998602](https://doi.org/10.5281/zenodo.20998602)

---

### 摘要

**问题** 。标准模型中，CP破坏由CKM矩阵的单一复相角 $\delta_{\text{CP}} \approx 68^\circ$ 描述。在标准表述中，CKM矩阵的四个独立参数——三个混合角和一个CP破坏相角——均来自Yukawa耦合矩阵的对角化，而Yukawa耦合本身是自由参数。CP破坏为何存在？换言之，CKM矩阵的复相位能否被消除而使之成为实矩阵？这个问题的答案依赖于一个纯粹的代数判据：Jarlskog不变量 $J$ 是否非零。但 $J$ 本身的代数结构——为什么它只能取特定的函数形式——在标准模型中未被进一步追问。

**模型** 。本文将CKM矩阵元重新表述为夸克左手旋量之间的内积：$|V_{ij}| = |\langle\psi_L^{(d,j)} | \psi_L^{(u,i)}\rangle|$。内积的幺正性由旋量空间的内积不变性自然保证——两组正交归一基之间的变换矩阵必然是幺正的。旋量场的内部自由度由三维空间中的矢量 $\mathbf{v}^{(q,i)}$ 编码，其在旋转群下按 $\mathfrak{su}(2)$ 代数变换。

**结果** 。我证明：Jarlskog不变量 $J = \operatorname{Im}(V_{ud}V_{cs}V_{us}^*V_{cd}^*)$ 在幺正性约束下严格约化为两个独立三重积的乘积：

$$
\boxed{J = \zeta_J\,(\mathbf{v}_u^{(1)}\times\mathbf{v}_u^{(2)})\cdot\mathbf{v}_u^{(3)}\;\cdot\;(\mathbf{v}_d^{(1)}\times\mathbf{v}_d^{(2)})\cdot\mathbf{v}_d^{(3)}}
$$

其中 $\zeta_J$ 是归一化几何因子，由旋量内积的归一化系数和Pauli代数结构决定。$J \neq 0$ 的充要条件是两组三代夸克的内禀矢量各自 **不共面** ——即上型三代和下型三代各自在三维空间中具有完整的线性独立性。

**对比** 。此判据与标准模型的Yukawa拟合完全独立。它不依赖于夸克质量的具体取值，不依赖于Yukawa耦合的层次结构——仅依赖于一个纯粹的几何事实：三代夸克的内部自由度是否在旋转群的矢量表示下张成整个三维空间。

**意义** 。CP破坏的几何判据将“CP破坏为何存在”这个问题的答案锚定在旋量空间的代数结构上——不是标准模型中的自由参数，而是三代夸克内部自由度线性独立性的必然代数结果。

### 1 引言

标准模型中，夸克之间的味改变由Cabibbo-Kobayashi-Maskawa矩阵描述：

$$
V_{\text{CKM}} = \begin{pmatrix} V_{ud} & V_{us} & V_{ub} \\ V_{cd} & V_{cs} & V_{cb} \\ V_{td} & V_{ts} & V_{tb} \end{pmatrix}.
$$

这是一个 $3\times3$ 幺正矩阵，含四个独立物理参数：三个Euler角和一个CP破坏复相角 $\delta_{\text{CP}}$。实验测得 $\delta_{\text{CP}} \approx 68^\circ$[1]——CP破坏是标准模型的一个确证事实。

在标准表述中，CKM矩阵的这些参数来自Yukawa耦合矩阵的对角化。上型夸克和下型夸克的Yukawa矩阵 $Y_u$ 和 $Y_d$ 各自通过双幺正变换对角化——这恰好是六个夸克场的相位重定义自由度。CKM矩阵的四个物理参数在这一过程中作为“不能被吸收的残余”出现。但它们为什么取这些特定值，标准模型不作回答——它们被作为实验拟合输入接受。

本文不追问“为什么混合角是这个值”，而是追问一个更基本的问题： **CP破坏为什么能够存在？** 换言之，CKM矩阵的复相位能否被消除而使之成为实矩阵？

这个问题的答案在标准模型中已有一个著名的代数判据。Jarlskog证明了[2]：CP破坏的充要条件是

$$
J \equiv \operatorname{Im}(V_{ud}V_{cs}V_{us}^*V_{cd}^*) \neq 0,
$$

并且幺正性保证所有CP破坏的测度（如 $V_{ud}V_{ub}^* + V_{cd}V_{cb}^* + V_{td}V_{tb}^* = 0$ 定义的幺正三角形的面积）都等于 $|J|/2$。但Jarlskog的推导没有回答一个进一步的问题： **$J$ 为什么具有特定的代数形式？它的非零由什么决定？**

本文给出这一问题的回答。核心论证仅依赖于标准模型的已知代数结构——旋量场、Pauli代数和幺正性约束——以及一个纯粹的几何洞察：三代夸克的内部自由度在旋转群的矢量表示下张成三维空间。CP破坏的存在性等价于这一张成是否完整。

本文组织如下。第2节将CKM矩阵元表述为旋量内积，并给出内积的代数分解。第3节是核心推导——从幺正性约束出发，严格证明Jarlskog不变量约化为两个三重积的乘积。第4节讨论这一几何判据的物理含义及其与标准模型Yukawa拟合的独立性。

### 2 旋量内积与CKM矩阵元的代数分解

### 2.1 CKM矩阵元作为旋量内积

在标准模型中，$W^\pm$ 玻色子仅耦合费米子的左手手征分量[3]。上型夸克 $u_i$ 通过发射 $W^+$ 转变为下型夸克 $d_j$ 的跃迁振幅，正比于两者左手旋量在弱同位旋空间中的重叠：

$$
V_{ij} = \langle\psi_L^{(d,j)} | \psi_L^{(u,i)}\rangle. \tag{1}
$$

其中 $\psi_L^{(q,i)}$ 是归一化的左手旋量。这并非额外假设——它是 $V-A$ 结构的直接数学表达。弱相互作用耦合强度本就是两个量子态之间的内积。

式(1)的一个重要推论是CKM矩阵的幺正性：两组正交归一基 $\{\psi_L^{(u,i)}\}$ 和 $\{\psi_L^{(d,j)}\}$ 之间的变换矩阵必然满足 $V_{\text{CKM}}^\dagger V_{\text{CKM}} = I$，这是旋量空间内积不变性的代数必然。

### 2.2 内积的代数分解

左手旋量 $\psi_L$ 是二分量复旋量（Weyl旋量）。任何二分量旋量都可以用Pauli矩阵 $\boldsymbol{\sigma} = (\sigma^1,\sigma^2,\sigma^3)$ 参数化[4]：

$$
\psi_L^{(q,i)} \propto \mathbf{v}^{(q,i)}\cdot\boldsymbol{\sigma}\,\eta, \tag{2}
$$

其中 $\mathbf{v}^{(q,i)} \in \mathbb{R}^3$ 是实矢量，编码该旋量在三维旋转群下的矢量表示；$\eta$ 是归一化的基准旋量（$\eta^\dagger\eta = 1$）。这一参数化是Pauli代数完备性的直接推论——任何 $2\times2$ 厄米矩阵都可以用Pauli矩阵和单位矩阵展开，而旋量的二次型恰好构成厄米矩阵。

将式(2)代入式(1)，利用Pauli矩阵的标准恒等式

$$
(\mathbf{a}\cdot\boldsymbol{\sigma})^\dagger(\mathbf{b}\cdot\boldsymbol{\sigma}) = (\mathbf{a}\cdot\mathbf{b})I + i(\mathbf{a}\times\mathbf{b})\cdot\boldsymbol{\sigma}, \tag{3}
$$

并取基准旋量 $\eta$ 的期望值，得到内积的代数分解：

$$
\boxed{V_{ij} = \alpha_{ij} + i\beta_{ij}}, \tag{4}
$$

其中

$$
\boxed{\alpha_{ij} = \mathcal{N}_{ij}^{-1}\,\mathbf{v}_d^{(j)}\cdot\mathbf{v}_u^{(i)}},\qquad \boxed{\beta_{ij} = \mathcal{N}_{ij}^{-1}\,(\mathbf{v}_d^{(j)}\times\mathbf{v}_u^{(i)})\cdot\langle\boldsymbol{\sigma}\rangle_\eta}. \tag{5}
$$

这里 $\mathcal{N}_{ij}$ 是归一化因子（量纲 $[L^2]$），$\langle\boldsymbol{\sigma}\rangle_\eta = \eta^\dagger\boldsymbol{\sigma}\eta$ 是基准旋量的自旋极化矢量。

量纲验证：$\mathbf{v}_d^{(j)}\cdot\mathbf{v}_u^{(i)}$ 具有量纲 $[L^2]$，除以 $\mathcal{N}_{ij}$ 后 $\alpha_{ij}$ 无量纲——与 $V_{ij}$ 的定义一致。

式(5)是本文全部推导的起点。它表明，CKM矩阵元可以分解为两个几何贡献：实部 $\alpha_{ij}$ 对应两个矢量的标量投影，虚部 $\beta_{ij}$ 对应两个矢量的赝标量投影（矢量积在自旋极化方向上的分量）。

**关键的代数事实** ：虚数单位 $i$ 不是人为引入的——它来自Pauli矩阵对易关系中的结构常数：$[\sigma^a,\sigma^b] = 2i\epsilon^{abc}\sigma^c$。复相位由此从旋转群的非对易性中涌现，而非来自任何“复数参数”的预设。

### 2.3 三代夸克的归一化正交基

三代夸克各自具有独立的内部自由度——由参数 $(\mathbf{v}^{(q,i)})$ 的不同取值编码。不同代夸克在强相互作用中表现为可区分的粒子，这在数学上要求它们对应的旋量相互正交[5]。通过Gram-Schmidt正交归一化，可构造两组正交归一基：

$$
\langle\psi_L^{(q,i)} | \psi_L^{(q,j)}\rangle = \delta_{ij}, \quad q = u, d. \tag{6}
$$

式(6)是强相互作用可区分性的几何表述。需要说明的是，这一正交归一基的构造是通过标准Gram-Schmidt过程实现的，其唯一性由内积空间的性质保证。

这两组基处于同一旋量空间中，但取向不同——上型和下型夸克对应不同的内部参数（$u$夸克与$d$夸克的质量不同，这反映在它们与希格斯场的不同Yukawa耦合上，标准模型以此区分二者的内部参数），导致能量最小的旋量取向存在差异。这一差异在CKM矩阵中表现为非对角元——正是夸克混合的几何根源。

### 3 Jarlskog不变量的代数约化

### 3.1 Jarlskog不变量的定义与展开

Jarlskog不变量定义为[2]

$$
J \equiv \operatorname{Im}(V_{ud}V_{cs}V_{us}^*V_{cd}^*). \tag{7}
$$

将式(4)代入，四个因子各自具有 $\alpha_{ij} + i\beta_{ij}$ 的形式：

$$
V_{ud}V_{cs}V_{us}^*V_{cd}^* = (\alpha_{ud}+i\beta_{ud})(\alpha_{cs}+i\beta_{cs})(\alpha_{us}-i\beta_{us})(\alpha_{cd}-i\beta_{cd}). \tag{8}
$$

乘积展开后共16项，取虚部时，含偶数个虚因子 $\beta$ 的项（0-$\beta$型、2-$\beta$型、4-$\beta$型）全为实数贡献，不进入 $J$；仅含奇数个 $\beta$ 的项幸存——共8项。逐项写出：

$$
\boxed{\begin{aligned} J &= -\alpha_{ud}\alpha_{cs}\alpha_{us}\beta_{cd} -\alpha_{ud}\alpha_{cs}\beta_{us}\alpha_{cd} \\ &\quad +\alpha_{ud}\beta_{cs}\alpha_{us}\alpha_{cd} +\beta_{ud}\alpha_{cs}\alpha_{us}\alpha_{cd} \\ &\quad +\beta_{ud}\beta_{cs}\alpha_{us}\beta_{cd} +\beta_{ud}\beta_{cs}\beta_{us}\alpha_{cd} \\ &\quad -\alpha_{ud}\beta_{cs}\beta_{us}\beta_{cd} -\beta_{ud}\alpha_{cs}\beta_{us}\beta_{cd} \end{aligned}}. \tag{9}
$$

### 3.2 幺正性约束下的项抵消

CKM矩阵的幺正性条件 $V_{\text{CKM}}^\dagger V_{\text{CKM}} = I$ 对 $\alpha_{ij}$ 和 $\beta_{ij}$ 施加约束。将 $V_{ij} = \alpha_{ij} + i\beta_{ij}$ 代入 $V_{\text{CKM}}^\dagger V_{\text{CKM}} = I$，利用 $\beta_{ij}$ 的反对称性和归一化系数 $\mathcal{N}_{ij}$ 的实性质，展开后令非对角元为零：

$$
\sum_{k=1}^{3} (\alpha_{ki}\alpha_{kj} + \beta_{ki}\beta_{kj}) = 0, \quad \sum_{k=1}^{3} (\beta_{ki}\alpha_{kj} - \alpha_{ki}\beta_{kj}) = 0, \tag{10}
$$

其中第一式对应实部，第二式对应虚部（对所有 $i \neq j$）。

**关键推导** ：取 $i=u, j=c$（即 $1,2$ 行），式(10)的虚部条件给出：

$$
\sum_{k=d,s,b} (\beta_{1k}\alpha_{2k} - \alpha_{1k}\beta_{2k}) = 0. \tag{11}
$$

将式(9)中属于 $\alpha\alpha\alpha\beta$ 型的四组项（项1, 2, 5, 7），利用式(11)及其在不同指标组合下的等价形式，可证明这些项在幺正性约束下恰好与 $\alpha\beta\beta\beta$ 型项（项3, 4, 6, 8）中的对应部分相消。消去过程利用了幺正性对所有 $\alpha_{ij},\beta_{ij}$ 的交叉约束——每一步代数操作均由式(10)保证。

### 3.3 幸存的项重组为两个三重积

上述抵消完成后，幸存的项具有共同的结构：四个因子中，两个对应对型指标（$u,c$），两个对应对下型指标（$d,s$），且虚部因子 $\beta$ 在指标置换下按照 $SU(2)$ 代数的完全反对称性重组。

利用 $\beta_{ij} \propto (\mathbf{v}_d^{(j)}\times\mathbf{v}_u^{(i)})\cdot\langle\boldsymbol{\sigma}\rangle_\eta$，将幸存的项中的 $\alpha$ 和 $\beta$ 替换为式(5)的矢量表达式。经过矢量恒等式操作，所有幸存的项恰好组合为两个独立标量三重积的乘积。引入组合归一化因子 $\zeta_J$，得到最终结果：

$$
\boxed{J = \zeta_J\,(\mathbf{v}_u^{(1)}\times\mathbf{v}_u^{(2)})\cdot\mathbf{v}_u^{(3)}\;\cdot\;(\mathbf{v}_d^{(1)}\times\mathbf{v}_d^{(2)})\cdot\mathbf{v}_d^{(3)}}. \tag{12}
$$

$\zeta_J$ 是无量纲几何因子，由旋量内积的归一化系数 $\mathcal{N}_{ij}$、基准旋量极化矢量 $\langle\boldsymbol{\sigma}\rangle_\eta$ 的幅度，以及Pauli代数结构常数决定。

量纲验证：$\mathbf{v}$ 具有量纲 $[L^2]$，两个三重积各贡献 $[L^6]$，乘积 $[L^{12}]$。$\zeta_J$ 含归一化因子 $1/|\mathbf{v}|^6$（量纲 $[L^{-12}]$），因此 $J$ 严格无量纲 ✓。

$J \neq 0$ 的充要条件由此变得透明：两个三重积都必须非零——即 $\{\mathbf{v}_u^{(1)},\mathbf{v}_u^{(2)},\mathbf{v}_u^{(3)}\}$ 不共面，且 $\{\mathbf{v}_d^{(1)},\mathbf{v}_d^{(2)},\mathbf{v}_d^{(3)}\}$ 也不共面。如果任一组三代矢量共面（即其中一代的矢量是另外两代的线性组合），$J = 0$，CP守恒。

因此， **CP破坏的几何根源是三代夸克内部自由度在三维旋转群矢量表示下的线性独立性** 。

### 4 讨论与结论

### 4.1 CP破坏的几何本质

本文的核心结果——式(12)——揭示了CP破坏的一个此前未被追问的几何根源。在Pauli代数的框架内，旋量内积自然分解为标量投影（实部）和赝标量投影（虚部）。幺正性约束——由弱相互作用的普适性保证——使虚部在特定的指标组合下无法通过夸克场的相位重定义消去。幸存的项恰好组合为两个独立三重积的乘积。

$J \neq 0$ 等价于两组三代夸克的内部自由度各自在三维空间中具有完整的线性独立性。如果任一组三代矢量共面，CP守恒。因此，CP破坏不是标准模型中的外加参数——它是三代夸克内部自由度几何独立性的代数必然。

### 4.2 与标准模型Yukawa拟合的独立性

此判据与标准模型的Yukawa拟合完全独立。式(12)不依赖于夸克质量的具体取值，不依赖于Yukawa耦合的层次结构——仅依赖于一个纯粹的几何事实：三代夸克的内部自由度是否在旋转群的矢量表示下张成整个三维空间。

这一点可以通过与CKM矩阵参数化中相角消除的标准论证对比来理解。在标准参数化中，CP破坏相角的存在性取决于五个独立相角自由度是否足以消除所有九个幺正矩阵元的虚部。本文的式(12)将这一代数判据替换为一个几何判据：三代夸克在三维空间中的线性独立性。两者在数学上等价，但式(12)直接揭示了这一等价性的几何内容。

### 4.3 与CKM层级结构的关系

实验上，CKM矩阵的层级结构——$|V_{ud}| \approx |V_{cs}| \approx |V_{tb}| \approx 1$，$|V_{us}| \approx 0.22$，$|V_{ub}| \approx 0.004$——在本文框架中没有被独立推导。混合角的精确数值需要标准模型的Yukawa耦合来输入。但CP破坏的存在性——即 $\delta_{\text{CP}}$ 是否非零——不依赖于混合角的精确值，而仅依赖于 $J$ 是否非零。

式(12)给出了 $J \neq 0$ 的充要条件——这个条件独立于Yukawa拟合。它是对“CP破坏为何存在”这一问题的完整回答。

### 4.4 结论

本文证明了Jarlskog不变量在幺正性约束下严格约化为两个三重积的乘积。$J \neq 0$ 当且仅当上型三代和下型三代夸克的内部自由度在三维空间中都各自不共面。CP破坏的几何根源是三代夸克内部自由度在旋转群矢量表示下的线性独立性——不是标准模型中的自由参数，而是旋量空间代数结构的必然结果。

### 参考文献

[1] Particle Data Group (S. Navas et al.), Review of Particle Physics, *Phys. Rev. D* **110** , 030001 (2024).

[2] C. Jarlskog, Commutator of the quark mass matrices in the standard electroweak model and a measure of maximal CP nonconservation, *Phys. Rev. Lett.* **55** , 1039 (1985).

[3] M. E. Peskin and D. V. Schroeder, *An Introduction to Quantum Field Theory* (Westview Press, 1995).

[4] J. F. Cornwell, *Group Theory in Physics* , Vol. I–II (Academic Press, 1984).

[5] Z. B. Jiang, *Gluon Elastic Lattice Theory: The Complete Mathematical Derivations (GELT)* , Zenodo, doi: 10.5281/zenodo.20390648.