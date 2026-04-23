# Libraries



# load libraries
library(tidyverse)
library(metaheuristicOpt)
library(minpack.lm)
library(furrr)
library(R.utils)
library(tictoc)
library(randtoolbox)



# WOA helper functions

# First we need to define this generateRandom(), calcFitness(), checkBound() functions, so Ive just copied them from the og package.


generateRandom <- function (numPopulation, dimension, lowerBound, upperBound)
{
    result <- matrix()
    if (length(lowerBound) == 1) {
        result <- matrix(runif(numPopulation * dimension, lowerBound,
            upperBound), nrow = numPopulation, ncol = dimension)
    }
    else {
        result <- matrix(nrow = numPopulation, ncol = dimension)
        for (i in 1:dimension) {
            result[, i] = runif(numPopulation, lowerBound[i],
                upperBound[i])
        }
    }
    return(result)
}



calcFitness <- function (FUN, optimType, popu)
{
    fitness <- c()
    for (i in 1:nrow(popu)) {
        fitness[i] <- optimType * FUN(popu[i, ])
    }
    return(fitness)
}



checkBound <- function (position, lowerBound, upperBound)
{
    check1 <- position > upperBound
    check2 <- position < lowerBound
    result <- (position * (!(check1 + check2))) + upperBound *
        check1 + lowerBound * check2
    return(result)
}


# SSE functions

## Sigmoidal


objective_SSE <- function(x, data) {
  h0 <- x[1]
  h1 <- x[2]
  t1 <- x[3]
  a  <- x[4]

  sse <- data |>
    mutate(preds = h0 + (h1 - h0)/(1 + exp(-a*(time - t1))),
           diff = (intensity - preds)^2) |>
    summarize(sse = sum(diff)) |>
    pull()

  return(sse)
}


## Double sigmoidal

# Im going to recreate f0 and f2_h0 with the desired parameters instead of weird B1, M1 etc.
#
# A2 = h2/h1
# Ka = h1
# B1 = a1
# M1 = t1
# B2 = a2
# L = t2 - t1
# h0 = h0


# f_base
f0 <- function(x, a1, t1, a2, t2) {
  1 / ((1 + exp(-a1 * (x - t1))) * (1 + exp(a2 * (x - (t1 + (t2 - t1))))))
}

# piecewise double sigmoid
f2_h0 <- function (x, h0, h1, h2, a1, t1, a2, t2, const, argument){
  fBasics::Heaviside(x - argument) * (f0(x, a1, t1, a2, t2) * ((h1 - (h2/h1) * h1)/(const)) + (h2/h1) * h1) +
    (1 - fBasics::Heaviside(x - argument)) * (f0(x, a1, t1, a2, t2) * ((h1 - h0)/(const)) + h0) }





double_sig_fit_formula <- function(time, h0, h1, h2, a1, a2, t1, t2){
  # A2 = h2/h1 # finalAsymptoteIntensityRatio
  # Ka = h1
  # B1 = a1
  # M1 = t1
  # B2 = a2
  # L = t2 - t1
  # h0 = h0

  # find x-value corresponding to max of f0 (which is t*)
  x_dense <- seq(min(time), max(time), length.out = 1000)
  f0_vals <- f0(x_dense, a1, t1, a2, t2)
  argument <- x_dense[which.max(f0_vals)]

  # const = f0
  const <- f0(argument, a1, t1, a2, t2) # argument because max(f0) is at t*

  f2_h0(time, h0, h1, h2, a1, t1, a2, t2, const, argument)

}



sse_func_double <- function(h0, h1, h2, a1, a2, t1, t2, data) {
  sse <- data |>
    mutate(preds = double_sig_fit_formula(data$time, h0, h1, h2, a1, a2, t1, t2),
           diff = (data$intensity - preds)^2) |>
    summarize(sse = sum(diff)) |>
    pull()
  return(sse)
}


# The only difference between `sse_func_double` and `objective_SSE_double` is that the former individual parameter estimates and the latter expects a vector.

# Ive also added checks to the function to make sure that h1 is positive, t2 is greater than t1, and a1 and a2 are non-zero.


objective_SSE_double <- function(x, data) {
  h0 <- x[1]; h1 <- x[2]; h2 <- x[3]
  a1 <- x[4]; a2 <- x[5]; t1 <- x[6]; t2 <- x[7]

  # check for invalid parameters
  if (h1 <= 0 ||
    t2 <= t1 ||
    any(c(a1, a2) <= 0) ||
    h1 <= h0 ||
    h1 <= h2) {

  return(1e10) # big sse
}


  # try-catch in case double_sig_fit_formula still produces NA
  sse <- tryCatch({
    sse_func_double(h0, h1, h2, a1, a2, t1, t2, data)
  }, error = function(e) {
    1e10
  })

  if(is.na(sse) || is.nan(sse) || is.infinite(sse)) sse <- 1e10

  return(sse)
}


# WOA sigmoidal variants

## Chaotic


engineWOA_chaotic <- function(FUN, optimType, maxIter, lowerBound, upperBound, whale) {
  whaleFitness <- calcFitness(FUN, optimType, whale)
  index <- order(whaleFitness)
  whaleFitness <- sort(whaleFitness)
  whale <- whale[index, ]
  bestPos <- whale[1, ]
  FbestPos <- whaleFitness[1]
  curve <- c()
  progressbar <- txtProgressBar(min = 0, max = maxIter, style = 3)

  # chaotic map
  chaotic_map <- function(x) 4 * x^3 - 3 * x

  # function to move range from (-1,1) to (0,1)
  to_unit <- function(x) (x + 1) / 2

  # starting value for r1, r2 - (-1,1) because that is domain of the map
  r1_val <- runif(1, -1, 1)
  r2_val <- runif(1, -1, 1)

  # back to regular function
  for (t in 1:maxIter) {
    a <- 2 - t * ((2) / maxIter)
    a2 <- -1 + t * ((-1) / maxIter)

    for (i in 1:nrow(whale)) {

      # update chaotic values
      r1_val <- chaotic_map(r1_val)
      r2_val <- chaotic_map(r2_val)


      # scale to [0,1]
      r1 <- to_unit(r1_val)
      r2 <- to_unit(r2_val)


      A <- 2 * a * r1 - a
      C <- 2 * r2
      b <- 1
      p  <- runif(1)
      l  <- (a2 - 1) * runif(1) + 1


      for (j in 1:ncol(whale)) {
        if (p < 0.5) {
          if (abs(A) >= 1) {
            rand.index <- floor(nrow(whale) * to_unit(chaotic_map(r1_val)) + 1)
            x.rand <- whale[rand.index, ]
            D.x.rand <- abs(C * x.rand[j] - whale[i, j])
            whale[i, j] <- x.rand[j] - A * D.x.rand
          } else {
            D.bestPos <- abs(C * bestPos[j] - whale[i, j])
            whale[i, j] <- bestPos[j] - A * D.bestPos
          }
        } else {
          distance <- abs(bestPos[j] - whale[i, j])
          whale[i, j] <- distance * exp(b * l) * cos(l * 2 * pi) + bestPos[j]
        }
      }

      whale[i, ] <- checkBound(whale[i, ], lowerBound, upperBound)
      fitness <- optimType * FUN(whale[i, ])
      if (fitness < FbestPos) {
        FbestPos <- fitness
        bestPos <- whale[i, ]
      }
    }
    curve[t] <- FbestPos
    setTxtProgressBar(progressbar, t)
  }
  close(progressbar)
  curve <- curve * optimType
  return(bestPos)
}



WOA_chaotic <- function(FUN, optimType = "MIN", numVar, numPopulation = 40,
  maxIter = 500, rangeVar)
{
  dimension <- ncol(rangeVar)
  lowerBound <- rangeVar[1, ]
  upperBound <- rangeVar[2, ]
  if (dimension == 1) {
    dimension <- numVar
  }
  if (optimType == "MAX")
    optimType <- -1
  else optimType <- 1
  whale <- generateRandom(numPopulation, dimension, lowerBound,
    upperBound)
  bestPos <- engineWOA_chaotic(FUN, optimType, maxIter, lowerBound,
    upperBound, whale)
  return(bestPos)
}



# run WOA_chaotic
run_WOA_chaotic <- function(data) {
  # running WOA_chaotic
  sse_result <- WOA_chaotic(
    FUN = function(x) objective_SSE(x, data),
    optimType = "MIN",
    numVar = ncol(bounds),
    numPopulation = 40,
    maxIter = 500,
    rangeVar = bounds
  )

  # compute best SSE at that solution
  best_sse <- objective_SSE(sse_result, data)

  # return both
  list(
    h0 = sse_result[1],
    h1 = sse_result[2],
    t1 = sse_result[3],
    a  = sse_result[4],
    best_sse = best_sse
  )
}


## Quasirandom


engineWOA_quasirandom <- function(FUN, optimType, maxIter, lowerBound, upperBound, whale) {
  whaleFitness <- calcFitness(FUN, optimType, whale)
  index <- order(whaleFitness)
  whaleFitness <- sort(whaleFitness)
  whale <- whale[index, ]
  bestPos <- whale[1, ]
  FbestPos <- whaleFitness[1]
  curve <- c()
  progressbar <- txtProgressBar(min = 0, max = maxIter, style = 3)

  # quasi-random sobol sequence
  dim_needed <- 2   # r1, r2
  sobol_seq <- sobol(n = maxIter, dim = dim_needed, scrambling = 0)


  # back to regular function
  for (t in 1:maxIter) {
    a <- 2 - t * ((2) / maxIter)
    a2 <- -1 + t * ((-1) / maxIter)

    for (i in 1:nrow(whale)) {

    r1 <- sobol_seq[t, 1]
    r2 <- sobol_seq[t, 2]


      A <- 2 * a * r1 - a
      C <- 2 * r2
      b <- 1
      p  <- runif(1)
      l  <- (a2 - 1) * runif(1) + 1


      for (j in 1:ncol(whale)) {
        if (p < 0.5) {
          if (abs(A) >= 1) {
            rand.index <- floor(nrow(whale) * r1) + 1
            x.rand <- whale[rand.index, ]
            D.x.rand <- abs(C * x.rand[j] - whale[i, j])
            whale[i, j] <- x.rand[j] - A * D.x.rand
          } else {
            D.bestPos <- abs(C * bestPos[j] - whale[i, j])
            whale[i, j] <- bestPos[j] - A * D.bestPos
          }
        } else {
          distance <- abs(bestPos[j] - whale[i, j])
          whale[i, j] <- distance * exp(b * l) * cos(l * 2 * pi) + bestPos[j]
        }
      }

      whale[i, ] <- checkBound(whale[i, ], lowerBound, upperBound)
      fitness <- optimType * FUN(whale[i, ])
      if (fitness < FbestPos) {
        FbestPos <- fitness
        bestPos <- whale[i, ]
      }
    }
    curve[t] <- FbestPos
    setTxtProgressBar(progressbar, t)
  }
  close(progressbar)
  curve <- curve * optimType
  return(bestPos)
}





WOA_quasirandom <- function(FUN, optimType = "MIN", numVar, numPopulation = 40,
  maxIter = 500, rangeVar)
{
  dimension <- ncol(rangeVar)
  lowerBound <- rangeVar[1, ]
  upperBound <- rangeVar[2, ]
  if (dimension == 1) {
    dimension <- numVar
  }
  if (optimType == "MAX")
    optimType <- -1
  else optimType <- 1
  whale <- generateRandom(numPopulation, dimension, lowerBound,
    upperBound)
  bestPos <- engineWOA_quasirandom(FUN, optimType, maxIter, lowerBound,
    upperBound, whale)
  return(bestPos)
}



run_WOA_quasirandom <- function(data) {
  # running WOA_quasirandom
  sse_result <- WOA_quasirandom(
    FUN = function(x) objective_SSE(x, data),
    optimType = "MIN",
    numVar = ncol(bounds),
    numPopulation = 40,
    maxIter = 500,
    rangeVar = bounds
  )

  # compute best SSE at that solution
  best_sse <- objective_SSE(sse_result, data)

  # return both
  list(
    h0 = sse_result[1],
    h1 = sse_result[2],
    t1 = sse_result[3],
    a  = sse_result[4],
    best_sse = best_sse
  )
}


## WOA


run_WOA <- function(data) {
  # running WOA
  sse_result <- WOA(
    FUN = function(x) objective_SSE(x, data),
    optimType = "MIN",
    numVar = ncol(bounds),
    numPopulation = 40,
    maxIter = 500,
    rangeVar = bounds
  )

  # compute best SSE at that solution
  best_sse <- objective_SSE(sse_result, data)

  # return both
  list(
    h0 = sse_result[1],
    h1 = sse_result[2],
    t1 = sse_result[3],
    a  = sse_result[4],
    best_sse = best_sse
  )
}


## Levy


levy_step <- function(n = 10000, beta = 1.5) {


  # same formula as above but lambda instead of beta
  sigma_u <- (gamma(1 + beta) * sin(pi * beta / 2) /
               (gamma((1 + beta) / 2) * beta * 2^((beta - 1) / 2)))^(1 / beta)

  # same u and v
  u <- rnorm(n, mean = 0, sd = sigma_u)
  v <- rnorm(n, mean = 0, sd = 1)

  # generate s
  s <- u / abs(v)^(1 / beta)

  return(s)
}



engine_WOA_levy_at_end <- function(FUN, optimType, maxIter, lowerBound, upperBound, whale) {
  whaleFitness <- calcFitness(FUN, optimType, whale)
  index <- order(whaleFitness)
  whaleFitness <- sort(whaleFitness)
  whale <- whale[index, ]
  bestPos <- whale[1, ]
  FbestPos <- whaleFitness[1]
  curve <- c()
  progressbar <- txtProgressBar(min = 0, max = maxIter, style = 3)
  for (t in 1:maxIter) {
    a <- 2 - t * ((2)/maxIter)
    a2 <- -1 + t * ((-1)/maxIter)
    for (i in 1:nrow(whale)) {
      r1 <- runif(1)
      r2 <- runif(1)
      A <- 2 * a * r1 - a
      C <- 2 * r2
      b <- 1
      l <- (a2 - 1) * runif(1) + 1
      p <- runif(1)
      for (j in 1:ncol(whale)) {
        if (p < 0.5) {
          if (abs(A) >= 1) {
            rand.index <- floor(nrow(whale) * runif(1) +
              1)
            x.rand <- whale[rand.index, ]
            D.x.rand <- abs(C * x.rand[j] - whale[i,
              j])
            whale[i, j] <- x.rand[j] - A * D.x.rand
          }
          else if (abs(A) < 1) {
            D.bestPos <- abs(C * bestPos[j] - whale[i,
              j])
            whale[i, j] <- bestPos[j] - A * D.bestPos
          }
        }
        else if (p >= 0.5) {
          distance <- abs(bestPos[j] - whale[i, j])
          whale[i, j] <- distance * exp(b * l) * cos(l *
            2 * pi) + bestPos[j]
        }
      }
      whale[i, ] <- checkBound(whale[i, ], lowerBound,
        upperBound)
      fitness <- optimType * FUN(whale[i, ])
      if (fitness < FbestPos) {
        FbestPos <- fitness
        bestPos <- whale[i, ]
      }
    }

# this is the levy part

scalar <- 0.01  # step-size scaling which we could tune...

for (i in 1:nrow(whale)) {
  # generate levy vector for each whale
  s <- levy_step(n = ncol(whale), beta = 1.5)

  # move whale by one levy step
  whale[i, ] <- whale[i, ] + scalar * s

  # check bounds
  whale[i, ] <- checkBound(whale[i, ], lowerBound, upperBound)

  # recalc fitness
  fitness <- optimType * FUN(whale[i, ])
  if (fitness < FbestPos) {
    FbestPos <- fitness
    bestPos <- whale[i, ]
  }
}
    # end of levy part
    curve[t] <- FbestPos
    setTxtProgressBar(progressbar, t)
  }
  close(progressbar)
  curve <- curve * optimType
  return(bestPos)
}




WOA_levy_at_end <- function(FUN, optimType = "MIN", numVar, numPopulation = 40,
  maxIter = 500, rangeVar)
{
  dimension <- ncol(rangeVar)
  lowerBound <- rangeVar[1, ]
  upperBound <- rangeVar[2, ]
  if (dimension == 1) {
    dimension <- numVar
  }
  if (optimType == "MAX")
    optimType <- -1
  else optimType <- 1
  whale <- generateRandom(numPopulation, dimension, lowerBound,
    upperBound)
  bestPos <- engine_WOA_levy_at_end(FUN, optimType, maxIter, lowerBound,
    upperBound, whale)
  return(bestPos)
}



run_WOA_levy <- function(data) {
  # Run WOA_levy_at_end optimization
  sse_result <- WOA_levy_at_end(
    FUN = function(x) objective_SSE(x, data),
    optimType = "MIN",
    numVar = ncol(bounds),
    numPopulation = 40,
    maxIter = 500,
    rangeVar = bounds
  )

  # Compute best SSE for that solution
  best_sse <- objective_SSE(sse_result, data)

  # Return parameter estimates and SSE
  list(
    h0 = sse_result[1],
    h1 = sse_result[2],
    t1 = sse_result[3],
    a  = sse_result[4],
    best_sse = best_sse
  )
}



## LMA


# first define SSE function
sse_func <- function(h0, h1, t1, a, data) {
  sse <- data |>
    mutate(preds = h0 + (h1 - h0) / (1 + exp(-a * (x - t1))),
      diff = (y - preds)^2) |>
    summarize(sse = sum(diff)) |>
    pull()
  return(sse)
}

# and sig_formula
sig_formula <- function(x, h0, h1, t1, a){
  h0 + (h1 - h0) / (1 + exp(-a * (x - t1)))
}



run_lma_fit <- function(data, dataset_id, seed) {
  # define bounds & starting values
  startlist <- list(h0 = 0.15, h1 = 0.75, t1 = 0.25, a = 90)
  lowerbounds <- c(h0 = -0.1, h1 = 0.3, t1 = -52, a = 0.01)
  upperbounds <- c(h0 = 0.35,  h1 = 0.97, t1 = 1, a = 180)

  # safely run LMA in case of convergence errors
  safe_nlsLM <- purrr::safely(minpack.lm::nlsLM, otherwise = NULL)

  result <- safe_nlsLM(
    intensity ~ sig_formula(time, h0, h1, t1, a),
    data = data,
    start = startlist,
    control = list(maxiter = 1000, factor = 100, ptol = 1e-8, ftol = 1e-8),
    lower = lowerbounds,
    upper = upperbounds,
    trace = FALSE
  )

  # If it failed, return NA row
  if (is.null(result$result)) {
    return(tibble(
      dataset_id = dataset_id,
      seed = seed,
      h0 = NA, h1 = NA, t1 = NA, a = NA,
      best_sse = NA,
      algorithm = "LMA"
    ))
  }

  # extract estimated parameters
  params <- coef(result$result)

  # compute SSE
  sse_val <- sse_func(
    h0 = params["h0"],
    h1 = params["h1"],
    t1 = params["t1"],
    a  = params["a"],
    data = data |> rename(x = time, y = intensity)
  )

  # return as tibble
  tibble(
    h0 = params["h0"],
    h1 = params["h1"],
    t1 = params["t1"],
    a  = params["a"],
    best_sse = sse_val,
    dataset_id = dataset_id,
    seed = seed,
    algorithm = "LMA"
  )
}






# WOA double sigmoidal variants

## Chaotic

run_WOA_chaotic_double <- function(data) {
  # running WOA_quasirandom
  sse_result <- WOA_chaotic(
    FUN = function(x) objective_SSE_double(x, data),
    optimType = "MIN",
    numVar = ncol(bounds),
    numPopulation = 40,
    maxIter = 500,
    rangeVar = bounds
  )

  # compute best SSE at that solution
  best_sse <- objective_SSE_double(sse_result, data)

  # return both
  list(
    h0 = sse_result[1],
    h1 = sse_result[2],
    h2 = sse_result[3],
    a1 = sse_result[4],
    a2 = sse_result[5],
    t1 = sse_result[6],
    t2 = sse_result[7],
    best_sse = best_sse
  )
}


## Quasirandom


run_WOA_quasirandom_double <- function(data) {
  # running WOA_quasirandom
  sse_result <- WOA_quasirandom(
    FUN = function(x) objective_SSE_double(x, data),
    optimType = "MIN",
    numVar = ncol(bounds),
    numPopulation = 40,
    maxIter = 500,
    rangeVar = bounds
  )

  # compute best SSE at that solution
  best_sse <- objective_SSE_double(sse_result, data)

  # return both
  list(
    h0 = sse_result[1],
    h1 = sse_result[2],
    h2 = sse_result[3],
    a1 = sse_result[4],
    a2 = sse_result[5],
    t1 = sse_result[6],
    t2 = sse_result[7],
    best_sse = best_sse
  )
}


## WOA


run_WOA_double <- function(data) {
  # running WOA_quasirandom
  sse_result <- WOA(
    FUN = function(x) objective_SSE_double(x, data),
    optimType = "MIN",
    numVar = ncol(bounds),
    numPopulation = 40,
    maxIter = 500,
    rangeVar = bounds
  )

  # compute best SSE at that solution
  best_sse <- objective_SSE_double(sse_result, data)

  # return both
  list(
    h0 = sse_result[1],
    h1 = sse_result[2],
    h2 = sse_result[3],
    a1 = sse_result[4],
    a2 = sse_result[5],
    t1 = sse_result[6],
    t2 = sse_result[7],
    best_sse = best_sse
  )
}


## Levy


run_WOA_levy_double <- function(data) {
  # Run WOA_levy_at_end optimization
  sse_result <- WOA_levy_at_end(
    FUN = function(x) objective_SSE_double(x, data),
    optimType = "MIN",
    numVar = ncol(bounds),
    numPopulation = 40,
    maxIter = 500,
    rangeVar = bounds
  )

  # Compute best SSE for that solution
  best_sse <- objective_SSE_double(sse_result, data)

  # Return parameter estimates and SSE
  list(
    h0 = sse_result[1],
    h1 = sse_result[2],
    h2 = sse_result[3],
    a1 = sse_result[4],
    a2 = sse_result[5],
    t1 = sse_result[6],
    t2 = sse_result[7],
    best_sse = best_sse
  )
}



## LMA

# double sigmoid lma
run_lma_fit_double <- function(data, dataset_id, seed,
                               max_success = 20, max_attempts = 500) {
  set.seed(seed)

  # bounds
  lowerbounds <- c(h0 = -0.10, h1 = 0.30, h2 = 0.00,
                   a1 = 0.01, a2 = 0.01,
                   t1 = -0.52, t2 = -0.48)
  upperbounds <- c(h0 = 0.30, h1 = 0.97, h2 = 1.00,
                   a1 = 180.00, a2 = 180.00,
                   t1 = 1.15, t2 = 1.79)

  # safe nlsLM
  safe_nlsLM <- purrr::safely(minpack.lm::nlsLM, otherwise = NULL)

  # store successful fits
  fits <- list()
  sse_values <- c()
  attempts <- 0

  while(length(fits) < max_success && attempts < max_attempts) {
    attempts <- attempts + 1

    # random start within bounds
    startlist <- lapply(names(lowerbounds), function(nm) {
      runif(1, min = lowerbounds[nm], max = upperbounds[nm])
    })
    names(startlist) <- names(lowerbounds)

    # make sure t2 > t1
    if(startlist$t2 <= startlist$t1) next

    # attempt nlsLM
    res <- safe_nlsLM(
      intensity ~ double_sig_fit_formula(time, h0, h1, h2, a1, a2, t1, t2),
      data = data,
      start = startlist,
      lower = lowerbounds,
      upper = upperbounds,
      control = list(maxiter = 1000, factor = 100, ptol = 1e-8, ftol = 1e-8),
      trace = FALSE
    )

    if(!is.null(res$result)) {
      # compute SSE
      params <- coef(res$result)
      sse_val <- objective_SSE_double(unname(params), data)

      fits[[length(fits)+1]] <- params
      sse_values <- c(sse_values, sse_val)
    }
  }

  if(length(fits) == 0) {
    # no successful fits
    return(tibble(
      dataset_id = dataset_id,
      seed = seed,
      h0 = NA, h1 = NA, h2 = NA,
      a1 = NA, a2 = NA,
      t1 = NA, t2 = NA,
      best_sse = NA,
      algorithm = "LMA_random"
    ))
  }

  # choose best fit (lowest SSE)
  best_idx <- which.min(sse_values)
  best_params <- fits[[best_idx]]

  tibble(
    dataset_id = dataset_id,
    seed = seed,
    h0 = best_params["h0"],
    h1 = best_params["h1"],
    h2 = best_params["h2"],
    a1 = best_params["a1"],
    a2 = best_params["a2"],
    t1 = best_params["t1"],
    t2 = best_params["t2"],
    best_sse = sse_values[best_idx],
    algorithm = "LMA_random"
  )
}



## LMA without random starts


# this is just to keep the old one - it shouldn't be used anywhere
# double sigmoid lma
run_lma_fit_double_no_random <- function(data, dataset_id, seed) {

  # define bounds & starting values
  startlist <- list(h0 = 0.15, h1 = 0.75, h2 = 0.5, a1 = 90, a2 = 90, t1 = 0.25, t2 = 0.3)
  lowerbounds <- c(h0 = -0.10, h1 = 0.30, h2 = 0.00, a1 = 0.01, a2 = 0.01, t1 = -0.52, t2 = -0.48)
  upperbounds <- c(h0 = 0.30, h1 = 0.97, h2 = 1.00, a1 = 180.00, a2 = 180.00, t1 = 1.15, t2 = 1.79)


  # safely run LMA in case of convergence errors
  safe_nlsLM <- purrr::safely(minpack.lm::nlsLM, otherwise = NULL)

  result <- safe_nlsLM(
    intensity ~ double_sig_fit_formula(time, h0, h1, h2, a1, a2, t1, t2),
    data = data,
    start = startlist,
    control = list(maxiter = 1000, factor = 100, ptol = 1e-8, ftol = 1e-8),
    lower = lowerbounds,
    upper = upperbounds,
    trace = FALSE
  )

  # If it failed, return NA row
  if (is.null(result$result)) {
    return(tibble(
      dataset_id = dataset_id,
      seed = seed,
      h0 = NA, h1 = NA, h2 = NA,
      a1 = NA, a2 = NA,
      t1 = NA, t2 = NA,
      best_sse = NA,
      algorithm = "LMA"
    ))
  }

  # extract estimated parameters
  params <- coef(result$result)

  # compute SSE
  params_vec <- c(
    params["h0"], params["h1"], params["h2"],
    params["a1"], params["a2"], params["t1"], params["t2"]
  )

  sse_val <- objective_SSE_double(params_vec, data)


  # return as tibble
  tibble(
    h0 = params["h0"],
    h1 = params["h1"],
    h2 = params["h2"],
    a1 = params["a1"],
    a2 = params["a2"],
    t1 = params["t1"],
    t2 = params["t2"],
    best_sse = sse_val,
    dataset_id = dataset_id,
    seed = seed,
    algorithm = "LMA"
  )
}






# Data Generation

## Sigmoidal


data_gen_func <- function(h0 = 30, h1 = 750, t1 = 160, a = 0.05, reps = 5, disp = 250){


  sig_formula <- function(x, h0, h1, t1, a){
    h0 + (h1 - h0) / (1 + exp(-a * (x - t1)))
  }

  x_vals <- rep(seq(0, 300, by = 20), times = reps)

  true_params <- list(h0 = h0, h1 = h1, t1 = t1, a = a)

  mean_vals <- rep(sig_formula(x_vals,
                               h0 = true_params$h0,
                               h1 = true_params$h1,
                               t1 = true_params$t1,
                               a = true_params$a))

  data <- rnorm(n = length(mean_vals), mean = mean_vals, sd = rep(disp, length(mean_vals)))
  sig_data <- data.frame(time = x_vals, intensity = data)

  # also want a normalized version
  norm_sig_data <- sig_data |>
    mutate(time = ((time - min(time))/(max(time)- min(time))),
           intensity = ((intensity - min(intensity))/(max(intensity)- min(intensity))))
}


## Double sigmoidal


# generate data
generate_piecewise_data <- function(x_vals = seq(0, 300, by = 20), reps = 5, dispersion = 10,
                                    a1 = 0.04, a2 = 0.03, t1 = 110, t2 = 240, h1 = 750, h2 = 400, h0 = 20) {


  # set.seed(101)

  # find x-value corresponding to max of f0 (which is t*)
  x_dense <- seq(min(x_vals), max(x_vals), length.out = 1000)
  f0_vals <- f0(x_dense, a1, t1, a2, t2)
  argument <- x_dense[which.max(f0_vals)]

  # const = f0
  const <- f0(argument, a1, t1, a2, t2) # argument because max(f0) is at t*

  # add reps to x and y
  x_repeated <- rep(x_vals, each = reps)
  y_true <- f2_h0(x_repeated, h0, h1, h2, a1, t1, a2, t2, const, argument)
  y_noisy <- rnorm(length(y_true), mean = y_true, sd = dispersion)

  # make df
  df <- data.frame(
    time = x_repeated,
    intensity = y_noisy)

  norm_df <- df |>
    mutate(time = ((time - min(time))/(max(time)- min(time))),
           intensity = ((intensity - min(intensity))/(max(intensity)- min(intensity))))

  return(norm_df)

}
