---
title: 质数计数函数Li(x)的改进
author: lizhisy
created: '2023-01-25'
source: http://zhuanlan.zhihu.com/p/600849452
---

李志 李华

**摘要** ：计算小于给定数量级质数个数的方法，最常用的是质数定理函数x/ln(x)和高斯函数Li(x)。但是两者对质数个数的估计前者总是小于，后者总是大于质数的实际个数，并且随着数量级的增加，偏差扩大。前文已经提出了对x/ln(x)进行改进的函数p(x)。现对高斯函数Li(x)进行动态修正，得到了一个更为理想的质数个数估计函数 q(x)。数值实验表明，与p(x)和黎曼函数R(x)计算结果比较，改进后的q（x）计算简便，且精确度较高。

**关键词** ：质数定理 质数个数 质数计数函数 动态修正

计算质数个数，最常用的是质数定理函数x/ln(x)和高斯函数Li(x)^（1）。高斯函数 Li(x) 表示为^（2）：

![](https://pica.zhimg.com/v2-e68a085d23509617be7cef54db0714a0_1440w.jpg)

高斯在1792年，勒让德在1798年就发现了质数定理^（2）。但是质数定理函数和高斯函数对质数个数的估计均存在较大偏差。前文已经对x/ln(x)进行了改进，获得了改进的质数估计函数p(x)^（3），表示为：

![](https://pic4.zhimg.com/v2-4ee0022e32783a4f63d012a32100067b_1440w.jpg)

其中：n=1.2为质数函数常数。

黎曼函数R(x) 的一种表示是^（4）：

![](https://pic1.zhimg.com/v2-ce53e6e9d28680c7ed97b3b16decb5c8_1440w.jpg)

![](https://pic1.zhimg.com/v2-3ee72e21395007a7ef4e031e7eac1e06_1440w.png)

黎曼函数的计算复杂，在给定数量级非常大时与Li(x)同样偏离真实值^（4）。因此有必要探索更为精确的质数计数函数。

质数的分布类型属于确定性随机分布^（5）。因此，理论上存在能够相对精确表示质数个数的函数。

现对高斯函数Li(x)进行动态修正，到了一个较理想的质数个数估计公式q(x)。数值实验表明，改进后的q(x)与p(x)和R(x)计算结果比较，它计算简便，且精确度较高。

### 一、小于给定数量级的质数个数

高斯函数Li(x)计算数值偏差较大，并总是大于实际的质数计数。本文对高斯Li(x)进行动态修正，在其积分式的分母上添加一个适当的正的函数，以减少积分式的值。经过大量实验，并进一步优化，确定了函数表达式，给出如下定义。

![](https://picx.zhimg.com/v2-443c07e0a6e77723eafc54745e52f14d_1440w.jpg)

### 一、实验验证

应用q(x)计算小于给定数量级的质数个数，并与应用p(x)和R(x)的计算结果进行比较，详见表1~表2和以及图1~图9。实验表明，很多情况下q(x)与 p(x) 和 R(x) 非常近似于质数计数函数π(x)，并随着 x 的增大，q(x)与 p(x) 和 R(x) 以及π(x) 互有交叉, q(x)表现了良好的逼近性能。q(x)函数形式简单，计算方便，且具有相对较高精确度。

![](https://pic3.zhimg.com/v2-222fdb9f269495619e9bc6e2b22822a4_1440w.jpg)

![](https://picx.zhimg.com/v2-36d038f763ece7bee65e4f127a57d1b9_1440w.jpg)

![](https://picx.zhimg.com/v2-bfd97aca8f9ff213abb0aec8b0918bb7_1440w.jpg)

![](https://pic1.zhimg.com/v2-07527205dd71aa6c8ab830801e32450a_1440w.jpg)

图1   棕色Li(x)，绿色q(x)，红色p(x)，蓝色π(x)，黑色R(x)，紫色x/ln(x)。

![](https://pica.zhimg.com/v2-ea93dfc92e6d975a11db1d2becac76d2_1440w.jpg)

图2  棕色Li(x)，绿色q(x)，红色p(x)，蓝色π(x)，黑色R(x)，紫色x/ln(x)。

![](https://pic4.zhimg.com/v2-deb21a53c5f8f9e34d6aa429aab8e893_1440w.jpg)

图3  绿色q(x)，红色p(x)，蓝色π(x)，黑色R(x)，紫色x/ln(x)。

![](https://pic1.zhimg.com/v2-a4de9958f18715fab6d7c989ffa5d1aa_1440w.jpg)

图4   绿色q(x)，红色p(x)，蓝色π(x)，黑色R(x)。

![](https://pic2.zhimg.com/v2-133041113d866c1440c7fedc6eaa9def_1440w.jpg)

图5   绿色q(x)，红色p(x)，蓝色π(x)，黑色R(x)。

![](https://pic1.zhimg.com/v2-cc14e0463fd1738442a7c0876de64b6c_1440w.jpg)

图6   绿色q(x)，红色p(x)，蓝色π(x)，黑色R(x)。

![](https://pic2.zhimg.com/v2-d19c16f68e255b34f83ab202933f0f7f_1440w.jpg)

图7   绿色q(x)，红色p(x)，蓝色π(x)，黑色R(x)。

![](https://pic2.zhimg.com/v2-60035bbf9c33ad9da6560c151285bbf1_1440w.jpg)

图8   绿色q(x)，红色p(x)，蓝色π(x)，黑色R(x)。

![](https://picx.zhimg.com/v2-fcbf7fc45510e540bba2cc1960bc064d_1440w.jpg)

图9   绿色q(x)，红色p(x)，蓝色π(x)，黑色R(x)。

### 三、讨论与结论

表1结果可见，应用q(x)计算小于给定数量级的质数个数相对较精确，优于应用p(x)和R(x)的计算结果。

表2结果可见，在给定区间内q(x)、p(x)和R(x)共有19组数据。q(x)与p(x)和R(x)计算值与π(x)计算值比较，q(x)与p(x)和R(x)变动方向完全一致，同步率达到100.00%；大于和小于π(x)计算值的分别为6组和13组，占31.58%和68.42%；其中q(x)有7组优于R(x)，占比达36.84%；q(x)有14组优于p(x)，占比达73.68%。

q(x)计算结果与p(x)和R(x)计算结果相近，但最大偏差和平均偏差均略优于R(x)。

表3结果可见，在给定区间内q(x)和R(x)共有3组数据。应用q(x)计算质数个数的偏差，其中有1组优于应用R(x)的计算结果。3组数据中最大偏差绝对值、平均偏差绝对值和标准差数值均比较小。

图1显示了六个函数之间在区间[10，1000]上的关系，Li(x)总是大于、x/ln(x)总是小于 p(x),q(x),π(x),和R(x)；而q(x),π(x),R(x)三者相互缠绕。图2~图9结果显示，q(x)与p(x)和R(x)的函数曲线与π(x)的函数曲线纠缠和穿越时常发生，表明计算不同区段质数个数时，会出现q(x)与p(x)和R(x)交替为优的情况。另外，q(x)与p(x)、π(x)和R(x)的函数曲线非常接近，拟合较佳。进而表明q(x)与p(x)和R(x)有很好的代表性。图4之后，由于x/ln(x)偏差较大，在图上已经不再出现。

因为质数的分布存在一定的随机性，实际质数个数始终在q(x)函数值的上下浮动，频繁变化，呈现波动状态。因此q(x)的函数曲线可称为质数曲线，q(x)可称为质数计数函数。

易知q(x)计算简便，精确度高于p(x)和R(x)的计算结果。q(x)是一个较为理想的质数计数函数，具有广泛的应用前景。

### 四、参考文献

[1] G. H.Hardy and E. M. Wright. An Introduction to the Theory of Numbers, 6th ed., Oxford University Press, 2008

[2] [https://mathworld.wolfram.com/PrimeCountingFunction.html](https://mathworld.wolfram.com/PrimeCountingFunction.html)

[3] Zhi Li and Hua Li.A Revised Prime Number Counting Function

. [https://vixra.org/abs/2301.0104](https://vixra.org/abs/2301.0104) .

[4] [https://primes.utm.edu/howmany.html](https://primes.utm.edu/howmany.html)

[5] Zhi Li and Hua Li.Proof of N^2+1 Conjecture. [https://vixra.org/abs/2209.0059](https://vixra.org/abs/2209.0059)