import math

class ThetaLinkSimulator:
    def simulate_theta_link(self, a, b, from_beta=1.0, to_beta=0.01):
        print(f"🌀 THETA-LINK: {a}, {b}")
        res_solid = a + b
        res_gas = (a**to_beta + b**to_beta)**(1/to_beta)
        print(f"Indeterminacy: {math.log(res_gas/res_solid):.4f}")

if __name__ == "__main__":
    ThetaLinkSimulator().simulate_theta_link(8, 9)
