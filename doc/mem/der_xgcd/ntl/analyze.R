library(tidyverse)
d <- read_csv("data.csv") %>%
  mutate(n = 2 ** n) %>%
  group_by(lib, n, threads) %>%
  summarise(us_per_n = mean(us_per_n), cpu_time = mean(cpu_time), real_time = mean(real_time)) %>%
  select(lib, n, threads, us_per_n, cpu_time, real_time) %>%
  mutate()

d %>%
  mutate(threads = as.factor(threads)) %>%
  ggplot(aes(x = n, y = us_per_n, color = threads, linetype = threads)) +
  facet_grid(cols = vars(lib), labeller = "label_both") +
  labs(
    title = "Computation Time",
    y = "Time (us/degree)",
    x = "Degree",
    color = "Library",
    linetype = "Library"
  ) +
  scale_x_continuous(trans = "log2") + 
  geom_line()


cs_per_xgcd_deg = 26
bellman_d <- read_csv("bellman_data.csv") %>%
  mutate(lib = "bellman") %>%
  mutate(n = 2 ** n) %>%
  mutate(time = time * n / 10 ** 6) %>%
  mutate(n = n / cs_per_xgcd_deg) %>%
  mutate()
read_csv("bellman_data.csv") %>%
  mutate(lib = "bellman") %>%
  mutate(time = time * 2**n / 10 ** 6) %>%
  filter(threads == 4) %>%
  mutate()

d %>%
  mutate(time = time / n)%>%
  ggplot(aes(x = n, y = time, color = lib, linetype = lib)) +
  facet_grid(cols = vars(threads), labeller = "label_both") +
  labs(
    title = "XGCD Computation Time",
    y = "Time (us/degree)",
    x = "Degree",
    color = "Library",
    linetype = "Library"
  ) +
  geom_line()

d %>%
  mutate(time = time / n)%>%
  bind_rows(bellman_d) %>%
  filter(threads >= 4) %>%
  ggplot(aes(x = n, y = time, color = lib, linetype = lib)) +
  facet_grid(cols = vars(threads), labeller = "label_both") +
  labs(
    title = "XGCD Computation Time",
    y = "Time (s)",
    x = "Degree",
    color = "Library",
    linetype = "Library"
  ) +
  scale_y_continuous(trans = "log2")+
  scale_x_continuous(trans = "log2")+
  geom_line()
