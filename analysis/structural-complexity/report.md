# Proof Completion structural-complexity metrics

Manifest tasks: **706**; computed: **706**.

## Coverage

- Reference proof found: 705
- Missing proof: 1
- Direct (no numbered steps): 215
- Structured: 490
- Obligations computed: 705
- Deps computed: 705

## Distributions

### Reference proof steps

Bands: `{'Direct': 215, '13-30': 116, '1-4': 127, '5-12': 167, '101+': 19, '31-50': 38, '51-100': 23}`

Structured summary: `{'metric': 'steps', 'n': 490, 'direct_or_zero_special': 215, 'min': 1, 'p25': 4.0, 'p50': 10.0, 'p75': 22.0, 'p90': 46.10000000000002, 'p95': 71.64999999999986, 'max': 1433, 'mean': 23.942857142857143}`

### Max proof depth

Hist: `{1: 208, 2: 128, 3: 63, 4: 46, 5: 20, 6: 9, 7: 11, 8: 3, 9: 2}`

Summary: `{'metric': 'max_depth', 'n': 490, 'direct_or_zero_special': 0, 'min': 1, 'p25': 1.0, 'p50': 2.0, 'p75': 3.0, 'p90': 4.0, 'p95': 5.5499999999999545, 'max': 9, 'mean': 2.2653061224489797}`

### Transitive proof dependencies

`{'metric': 'transitive_deps', 'n': 705, 'direct_or_zero_special': 0, 'min': 0, 'p25': 3.0, 'p50': 9.0, 'p75': 21.0, 'p90': 42.0, 'p95': 55.0, 'max': 263, 'mean': 16.890780141843972}`

### Reference proof obligations

`{'metric': 'obligations', 'n': 705, 'direct_or_zero_special': 0, 'min': 1, 'p25': 3.0, 'p50': 11.0, 'p75': 31.0, 'p90': 81.0, 'p95': 136.5999999999999, 'max': 2780, 'mean': 36.94751773049645}`

## Spearman (structured tasks with all metrics)

n=490 corr=`{'steps_vs_depth': 0.8590891782077482, 'steps_vs_deps': 0.34007368669274834, 'steps_vs_obligations': 0.9741162448960529, 'depth_vs_deps': 0.23202790836384546, 'depth_vs_obligations': 0.8027437232374687, 'deps_vs_obligations': 0.36767116921376874}`

## Composer 2.5 pass-rate trends

```json
{
  "by_steps": {
    "1-4": {
      "n": 94,
      "pass_rate": 0.8085106382978723
    },
    "13-30": {
      "n": 79,
      "pass_rate": 0.5822784810126582
    },
    "31+": {
      "n": 53,
      "pass_rate": 0.32075471698113206
    },
    "5-12": {
      "n": 91,
      "pass_rate": 0.7802197802197802
    },
    "Direct": {
      "n": 132,
      "pass_rate": 0.8863636363636364
    }
  },
  "by_depth": {
    "1": {
      "n": 124,
      "pass_rate": 0.7903225806451613
    },
    "2": {
      "n": 76,
      "pass_rate": 0.7894736842105263
    },
    "3": {
      "n": 45,
      "pass_rate": 0.5111111111111111
    },
    "4+": {
      "n": 72,
      "pass_rate": 0.4027777777777778
    },
    "Direct": {
      "n": 132,
      "pass_rate": 0.8863636363636364
    }
  },
  "by_deps": {
    "0-2": {
      "n": 118,
      "pass_rate": 0.9152542372881356
    },
    "21+": {
      "n": 72,
      "pass_rate": 0.4166666666666667
    },
    "3-8": {
      "n": 124,
      "pass_rate": 0.7903225806451613
    },
    "9-20": {
      "n": 134,
      "pass_rate": 0.6716417910447762
    },
    "missing": {
      "n": 1,
      "pass_rate": 1.0
    }
  },
  "by_obligations": {
    "0-1": {
      "n": 69,
      "pass_rate": 0.927536231884058
    },
    "13+": {
      "n": 185,
      "pass_rate": 0.5513513513513514
    },
    "2-4": {
      "n": 69,
      "pass_rate": 0.8840579710144928
    },
    "5-12": {
      "n": 125,
      "pass_rate": 0.792
    },
    "missing": {
      "n": 1,
      "pass_rate": 1.0
    }
  }
}
```

## Residual signal within steps/depth bands

```json
{
  "steps": {
    "13-30": {
      "n_pass": 46,
      "n_fail": 33,
      "deps_mean_pass": 8.91304347826087,
      "deps_mean_fail": 15.121212121212121,
      "obl_mean_pass": 37.97826086956522,
      "obl_mean_fail": 44.93939393939394
    },
    "Direct": {
      "n_pass": 117,
      "n_fail": 15,
      "deps_mean_pass": 4.512820512820513,
      "deps_mean_fail": 9.133333333333333,
      "obl_mean_pass": 1.7692307692307692,
      "obl_mean_fail": 2.8
    },
    "1-4": {
      "n_pass": 75,
      "n_fail": 18,
      "deps_mean_pass": 11.173333333333334,
      "deps_mean_fail": 14.38888888888889,
      "obl_mean_pass": 6.92,
      "obl_mean_fail": 7.5
    },
    "5-12": {
      "n_pass": 71,
      "n_fail": 20,
      "deps_mean_pass": 9.183098591549296,
      "deps_mean_fail": 14.25,
      "obl_mean_pass": 15.225352112676056,
      "obl_mean_fail": 16.95
    },
    "31+": {
      "n_pass": 17,
      "n_fail": 36,
      "deps_mean_pass": 17.352941176470587,
      "deps_mean_fail": 27.38888888888889,
      "obl_mean_pass": 136.94117647058823,
      "obl_mean_fail": 315.3611111111111
    }
  },
  "depth": {
    "2": {
      "n_pass": 60,
      "n_fail": 16,
      "deps_mean_pass": 10.966666666666667,
      "deps_mean_fail": 12.0625,
      "obl_mean_pass": 22.166666666666668,
      "obl_mean_fail": 28.0
    },
    "Direct": {
      "n_pass": 117,
      "n_fail": 15,
      "deps_mean_pass": 4.512820512820513,
      "deps_mean_fail": 9.133333333333333,
      "obl_mean_pass": 1.7692307692307692,
      "obl_mean_fail": 2.8
    },
    "1": {
      "n_pass": 97,
      "n_fail": 26,
      "deps_mean_pass": 10.206185567010309,
      "deps_mean_fail": 12.807692307692308,
      "obl_mean_pass": 8.329896907216495,
      "obl_mean_fail": 8.653846153846153
    },
    "4+": {
      "n_pass": 29,
      "n_fail": 43,
      "deps_mean_pass": 12.310344827586206,
      "deps_mean_fail": 25.441860465116278,
      "obl_mean_pass": 92.13793103448276,
      "obl_mean_fail": 271.3255813953488
    },
    "3": {
      "n_pass": 23,
      "n_fail": 22,
      "deps_mean_pass": 8.26086956521739,
      "deps_mean_fail": 18.59090909090909,
      "obl_mean_pass": 37.608695652173914,
      "obl_mean_fail": 44.09090909090909
    }
  }
}
```

