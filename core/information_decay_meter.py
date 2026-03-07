import math

class InformationDecayMeter:
    def calculate_logical_entropy(self, value):
        if value <= 1: return 0
        binary = bin(value)[2:]
        counts = {'0': binary.count('0'), '1': binary.count('1')}
        total = len(binary)
        return -sum((count/total) * math.log2(count/total) for count in counts.values() if count > 0)

    def measure_decay(self, name, sequence):
        print(f"🌡️ MEASURING INFORMATION DECAY: {name}")
        entropies = [self.calculate_logical_entropy(v) for v in sequence]
        total_decay = entropies[0] - entropies[-1]
        print(f"Total Logic Information Dissipated: {total_decay:.4f}")
        print(f"Status: {'DECAYING (Stable)' if total_decay > 0 else 'EXCITED (Axiomatic)'}")

if __name__ == "__main__":
    meter = InformationDecayMeter()
    n, seq = 27, [27]
    while n != 1:
        n = n // 2 if n % 2 == 0 else 3 * n + 1
        seq.append(n)
    meter.measure_decay("Collatz Orbit (n=27)", seq)
