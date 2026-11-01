"""复现论文的显式高斯测量；浮点检查不代替解析证明。"""
from pathlib import Path
import argparse
import json
import numpy as np
from scipy.optimize import brentq
from scipy.special import gammaln


def seeds(j, t):
    """每列概率密度对整个实轴的积分在解析上严格等于一。"""
    big_j = j + 0.5
    epsilon = 1 / np.log(np.e + big_j)
    m = np.arange(-j, j + 1)
    variance = (big_j**2 - m**2) / (2 * np.sqrt(m**2 + (epsilon * big_j)**2))
    amplitude = np.exp(-(np.asarray(t)[..., None] - m)**2 / (4 * variance))
    amplitude /= (2 * np.pi * variance)**0.25
    return amplitude, m, variance, epsilon


def evaluate(j, step=0.2):
    if j == 0:
        return {"j": 0, "V": 0, "fisher_trace": 0, "NH_lower_V": 0}
    big_j = j + 0.5
    _, m, variance, epsilon = seeds(j, [0.0])
    c = np.sqrt((j - m[:-1]) * (j + m[:-1] + 1))
    second = j * (j + 1) - m**2
    margin = 12 * np.sqrt(np.max(variance))
    n = int(np.ceil((2 * j + 2 * margin) / step))
    t = np.linspace(-j - margin, j + margin, n + 1)
    dt = t[1] - t[0]
    columns = np.zeros(len(m))
    total_cost = total_trial = total_information = 0.0
    for start in range(0, len(t), 512):
        tt = t[start:start + 512]
        amplitude = seeds(j, tt)[0]
        density = amplitude**2
        norm = density.sum(axis=1)
        first = (amplitude[:, :-1] * amplitude[:, 1:]) @ c
        second_numerator = density @ second
        signal = np.divide(first**2, norm, out=np.zeros_like(first), where=norm > 1e-280)
        trial_mean = np.sqrt(np.maximum(big_j**2 - tt**2, 0))
        weights = np.ones(len(tt)) * dt
        if start == 0:
            weights[0] *= 0.5
        if start + len(tt) == len(t):
            weights[-1] *= 0.5
        columns += weights @ density
        total_cost += weights @ (second_numerator - signal)
        total_information += weights @ (4 * signal)
        total_trial += weights @ (second_numerator - 2 * trial_mean * first + trial_mean**2 * norm)
    d = len(m)
    tau = brentq(lambda z: np.maximum(c - z, 0).sum() - z, 0, float(c.max()))
    lower = float((c * np.maximum(c - tau, 0)).sum() / d)
    return {
        "j": j, "epsilon": float(epsilon), "step": step,
        "V": total_cost / d, "V_over_j": total_cost / d / j,
        "trial_over_j": total_trial / d / j, "NH_lower_V": lower,
        "fisher_trace": total_information / d,
        "column_integral_max_error": float(np.max(abs(columns - 1))),
        "trace_identity_absolute_error": float(abs(total_information / d - (8 * j * (j + 1) / 3 - 4 * total_cost / d))),
        "trace_identity_relative_error": float(abs(total_information / d - (8 * j * (j + 1) / 3 - 4 * total_cost / d)) / max(1, total_information / d)),
    }


def check_full_matrices(j):
    """直接矩阵积分核对相位符号、完备性、Fisher 和 score 无偏性。"""
    _, m, variance, _ = seeds(j, [0])
    d = len(m)
    phase_count = max(d, 3)
    margin = 12 * np.sqrt(variance.max())
    t = np.linspace(-j - margin, j + margin, 1601)
    weights = np.full(len(t), t[1] - t[0])
    weights[[0, -1]] *= 0.5
    amplitude = seeds(j, t)[0]
    norm = (amplitude**2).sum(axis=1)
    c = np.sqrt((j - m[:-1]) * (j + m[:-1] + 1))
    raising = np.diag(c, -1)
    jx = (raising + raising.T) / 2
    jy = (raising - raising.T) / (2j)
    completeness = np.zeros((d, d), dtype=complex)
    fisher = np.zeros((2, 2))
    score_mean = np.zeros(2)
    sign_error = 0.0
    h = (amplitude[:, :-1] * amplitude[:, 1:]) @ c
    for ell in range(phase_count):
        phi = 2 * np.pi * ell / phase_count
        v = amplitude * np.exp(-1j * m * phi)
        completeness += np.einsum("t,tm,tn->mn", weights / phase_count, v, v.conj())
        p = norm / (d * phase_count)
        gradients = np.column_stack([
            2 * np.einsum("ti,ij,tj->t", v.conj(), operator, v).real / (d * phase_count)
            for operator in (jx, jy)
        ])
        score = np.divide(gradients, p[:, None], out=np.zeros_like(gradients), where=p[:, None] > 1e-280)
        expected_score = np.divide(2 * h, norm, out=np.zeros_like(h), where=norm > 1e-280)[:, None]
        expected_score = expected_score * np.array([np.cos(phi), np.sin(phi)])
        sign_error = max(sign_error, float(np.max(abs(score - expected_score))))
        fisher += np.einsum("t,ti,tj->ij", weights * p, score, score)
        score_mean += (weights * p) @ score
    inverse = np.linalg.inv(fisher)
    result = {
        "j": j,
        "completeness_error": float(np.max(abs(completeness - np.eye(d)))),
        "score_formula_error": sign_error,
        "score_mean_error": float(np.max(abs(score_mean))),
        "isotropy_error": float(np.max(abs(fisher - np.trace(fisher) * np.eye(2) / 2))),
        "local_unbiased_jacobian_error": float(np.max(abs(inverse @ fisher - np.eye(2)))),
        "fisher_eigenvalue_min": float(np.linalg.eigvalsh(fisher)[0]),
    }
    assert result["completeness_error"] < 1e-10
    assert result["score_formula_error"] < 1e-10
    assert result["score_mean_error"] < 1e-10
    assert result["isotropy_error"] < 1e-10
    assert result["fisher_eigenvalue_min"] > 0
    return result


def finite_copy_cost(n, cache):
    js = np.arange(n % 2 / 2, n / 2 + 1)
    k = n / 2 - js
    logbinomial = gammaln(n + 1) - gammaln(k + 1) - gammaln(n - k + 1)
    weights = (2 * js + 1)**2 / (n / 2 + js + 1) * np.exp(logbinomial - n * np.log(2))
    for j in js:
        if j not in cache:
            cache[j] = evaluate(float(j))
    v = sum(p * cache[j]["V"] for p, j in zip(weights, js))
    nhv = sum(p * cache[j]["NH_lower_V"] for p, j in zip(weights, js))
    meanj = weights @ js
    cost = 4 * n / (2 * n - 4 * v)
    nh = 4 * n / (2 * n - 4 * nhv)
    coherent = 4 * n / (2 * n - 8 * meanj / 3)
    return {"N": n, "C_construction": cost, "C_NH_lower": nh,
            "C_coherent": coherent, "A_construction": np.sqrt(n) * (cost - 2),
            "A_NH_lower": np.sqrt(n) * (nh - 2), "weight_sum_error": float(abs(weights.sum() - 1))}


def make_figure(data, path):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 10,
                         "axes.spines.top": False, "axes.spines.right": False})
    fig, axes = plt.subplots(1, 2, figsize=(10.8, 4.0), constrained_layout=True)
    sectors = data["sectors"]
    x = [r["j"] for r in sectors]
    axes[0].plot(x, [r["V_over_j"] for r in sectors], "o-", color="#176d8c", label="Explicit Gaussian POVM")
    axes[0].plot(x, [r["NH_lower_V"] / r["j"] for r in sectors], "s--", color="#a85c31", label="All-POVM lower bound")
    axes[0].axhline(2/3, ls=":", color="#7c8792", label="Coherent POVM")
    axes[0].axhline(0.5, ls="--", color="#28354a", label="Proved optimal limit: 1/2")
    axes[0].set(xscale="log", xlabel="Spin j", ylabel="Average planar variance / j")
    axes[0].legend(fontsize=8)
    copies = data["finite_copy"]
    axes[1].plot([r["N"] for r in copies], [r["A_construction"] for r in copies], "o-", color="#176d8c", label="Explicit Gaussian POVM")
    axes[1].plot([r["N"] for r in copies], [r["A_NH_lower"] for r in copies], "s--", color="#a85c31", label="NH lower bound")
    axes[1].axhline(np.sqrt(8/np.pi), color="#28354a", ls="--", label=r"Proved optimal limit: $\sqrt{8/\pi}$")
    axes[1].set(xscale="log", xlabel="Copies N", ylabel=r"$\sqrt{N}(C-2)$")
    axes[1].legend(fontsize=8)
    for ax in axes:
        ax.grid(alpha=0.18)
    fig.savefig(path, dpi=220)
    plt.close(fig)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--no-plot", action="store_true")
    args = parser.parse_args()
    directory = Path(__file__).resolve().parent
    spins = [0.5, 1, 2, 5, 10, 20, 50, 100, 300, 1000, 3000]
    sectors = [evaluate(j) for j in spins]
    fine = evaluate(100, step=0.1)
    convergence_difference = abs(fine["V"] - next(r["V"] for r in sectors if r["j"] == 100))
    assert convergence_difference < 1e-8
    for row in sectors:
        assert row["column_integral_max_error"] < 1e-9
        assert row["trace_identity_relative_error"] < 1e-9
        assert row["V"] + 1e-8 >= row["NH_lower_V"]
    cache = {r["j"]: r for r in sectors}
    data = {"method": "Floating-point diagnostics; theorem is analytic. Full real-line Gaussian POVMs; numerical tail truncation is diagnostic only.",
            "epsilon_rule": "1/log(e+j+1/2)", "sectors": sectors,
            "matrix_checks": [check_full_matrices(j) for j in [0.5, 1, 1.5, 2, 3]],
            "quadrature_step_halving_V_difference_j100": convergence_difference,
            "finite_copy": [finite_copy_cost(n, cache) for n in [1, 2, 5, 10, 20, 50, 100, 200, 400]]}
    (directory / "verification_results.json").write_text(json.dumps(data, indent=2), encoding="utf-8")
    if not args.no_plot:
        make_figure(data, directory / "precision_scaling.png")
    print(json.dumps({"sector_count": len(sectors), "matrix_checks": len(data["matrix_checks"]),
                      "max_column_error": max(r["column_integral_max_error"] for r in sectors),
                      "step_halving_V_difference": convergence_difference,
                      "largest_spin": sectors[-1], "largest_N": data["finite_copy"][-1]}, indent=2))
