library(tidyverse)
d <- read_csv("data.csv")
d %>%
    group_by(lib, n, threads) %>%
    summarise(s_xgcd = mean(s_xgcd)) %>%
    mutate(us_per_n_xgcd = s_xgcd / (2 ** n) * 10 ** 6) %>%
    filter(threads == 4) %>%
    mutate()
