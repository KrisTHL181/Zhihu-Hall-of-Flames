---
title: Derivation of Gravitational Potential and Gravitational Redshift in the All-Space
  Horizon Model
author: 嘉木
created: '2026-02-21'
source: http://zhuanlan.zhihu.com/p/2008664975875539211
---

本文采用静态球对称时空框架，以宇宙总质量密度为基本出发点，严格推导引力势差与精确引力红移关系。全过程不引入弱场近似，不预设引力场强的具体形式。定义宇宙物质能量密度为 $\rho(r)$ ，引力场等效能量密度为 D(r)，二者之和为总引力质量密度 $\mu(r) = \rho(r) + D(r)$ 。为满足时空自洽条件——即径向坐标 r=0 处形成宇宙视界，观测者所在位置 r=R 处时空趋于平直，总质量密度取如下分布形式：

$\mu(r) = \frac{c^2}{4\pi G r^2}$

其中 c 为真空中的光速，G 为万有引力常数，R 为观测者所在的特征径向尺度。半径 r 内包含的总引力质量 M(r) 由球对称体积分给出：

$M(r) = \int_0^r \mu(r') \cdot 4\pi r'^2 \mathrm{d}r'$

将总质量密度代入积分式并化简，可得质量分布的精确表达式：

$M(r) = \int_0^r \frac{c^2}{4\pi G r'^2} \cdot 4\pi r'^2 \mathrm{d}r' = \int_0^r \frac{c^2}{G} \mathrm{d}r' = \frac{c^2}{G} r$

在静态球对称时空中，引力势 $\Phi(r)$ 的径向梯度满足泊松方程的积分约束，其关系为：

$\frac{\mathrm{d}\Phi}{\mathrm{d}r} = \frac{G M(r)}{r^2}$

将上述质量分布 M(r) 代入上式，得到引力势的径向梯度：

$\frac{\mathrm{d}\Phi}{\mathrm{d}r} = \frac{c^2}{r}$

定义观测点 r=R 与光源发射点 r 之间的引力势差为 \Delta\Phi = \Phi(R) - \Phi(r)。根据引力势的定义，势差可通过对引力势梯度沿径向路径积分得到：

$\Delta\Phi = \int_{r}^{R} \frac{\mathrm{d}\Phi}{\mathrm{d}r'} \mathrm{d}r' = \int_{r}^{R} \frac{c^2}{r'} \mathrm{d}r'$

计算该积分，得到精确的引力势差表达式：

$\Delta\Phi = c^2 \ln\frac{R}{r}$

依据广义相对论中静态时空的精确引力红移定律，红移量 z 与引力势差满足如下关系：

$1+z = \exp\left(\frac{\Delta\Phi}{c^2}\right)$

将上述精确势差 $\Delta\Phi$ 代入红移公式，利用指数与对数的恒等关系化简后可得：

$1+z = \exp\left(\ln\frac{R}{r}\right) = \frac{R}{r}$

最终得到全时空视界宇宙模型的精确引力红移定律：

$\boxed{z = \frac{R}{r} - 1}$

In this paper, we adopt the framework of a static spherically symmetric spacetime and strictly derive the gravitational potential difference and the exact gravitational redshift relation based on the total mass density of the universe. The entire derivation does not introduce weak-field approximations or preset specific forms of the gravitational field strength. We define the cosmic matter energy density as $\rho(r)$ and the equivalent energy density of the gravitational field as D(r); their sum is the total gravitational mass density $\mu(r) = \rho(r) + D(r)$ . To satisfy the spacetime self-consistency condition—namely, a cosmic horizon forms at r=0 (radial coordinate) and the spacetime tends to be flat at the observer's location r=R, the total mass density takes the following self-consistent distribution:

$\mu(r) = \frac{c^2}{4\pi G r^2}$

where c is the speed of light in vacuum, G is the gravitational constant, and R is the characteristic radial scale of the observer's position. The total gravitational mass M(r) enclosed within a radius r is given by the spherical volume integral:

$M(r) = \int_0^r \mu(r') \cdot 4\pi r'^2 \mathrm{d}r'$

Substituting the total mass density into the integral and simplifying, we obtain the exact expression for the mass distribution:

$M(r) = \int_0^r \frac{c^2}{4\pi G r'^2} \cdot 4\pi r'^2 \mathrm{d}r' = \int_0^r \frac{c^2}{G} \mathrm{d}r' = \frac{c^2}{G} r$

In a static spherically symmetric spacetime, the radial gradient of the gravitational potential \Phi(r) satisfies the integral constraint of the Poisson equation, with the relation:

$\frac{\mathrm{d}\Phi}{\mathrm{d}r} = \frac{G M(r)}{r^2}$

Substituting the aforementioned mass distribution M(r) into the above equation yields the radial gradient of the gravitational potential:

$\frac{\mathrm{d}\Phi}{\mathrm{d}r} = \frac{c^2}{r}$

We define the gravitational potential difference between the observer's position r=R and the light source's emission position r as \Delta\Phi = \Phi(R) - \Phi(r). According to the definition of gravitational potential, the potential difference can be obtained by integrating the radial gradient of the gravitational potential along the radial path:

$\Delta\Phi = \int_{r}^{R} \frac{\mathrm{d}\Phi}{\mathrm{d}r'} \mathrm{d}r' = \int_{r}^{R} \frac{c^2}{r'} \mathrm{d}r'$

Evaluating this integral gives the exact expression for the gravitational potential difference:

$\Delta\Phi = c^2 \ln\frac{R}{r}$

According to the exact gravitational redshift law for static spacetimes in general relativity, the redshift z and the gravitational potential difference satisfy the following relation:

$1+z = \exp\left(\frac{\Delta\Phi}{c^2}\right)$

Substituting the exact potential difference \Delta\Phi into the redshift formula and simplifying using the identity between the exponential and logarithmic functions, we obtain:

$1+z = \exp\left(\ln\frac{R}{r}\right) = \frac{R}{r}$

Finally, we derive the exact gravitational redshift law for the all-space horizon cosmic model:

$\boxed{z = \frac{R}{r} - 1}$