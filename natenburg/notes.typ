#set heading(numbering: "1.")
#set enum(numbering: "1.a)")

#import "@preview/ilm:1.4.0": *
#import "../preamble.typ" : *
#show: thmrules

#show: ilm.with(
  title: [Options],
  author: "Rohan Jain",
  date: datetime(year: 2024, month: 03, day: 19),
  preface: [
    #align(center + horizon)[
      Put-call-parity more like phencyclidine
    ]
  ],
  table-of-contents: none,
)
#set math.equation(numbering: none)

#pagebreak()
#toc
#counter(page).update(1)
#pagebreak()
#counter(page).update(1)
= The Language of Options
== Contracts
#definition[
  There are two types of options, call and put. A call gives the holder the right to buy an asset at a strike price, while a put gives the holder the right to sell an asset at a strike price.
]
Note that options are different from futures contracts. With a futures contract, the buyer and the seller both have obligations; the seller must make delivery of the asset and the buyer must take delivery. With options, however, the buyer _has a choice_ to take delivery (call) or make delivery (put). If the buyer chooses to make an action, then the seller has an obligation to fulfill the contract. 

#definition[
  The asset to be bought or sold under the terms of the option is called the underlying. The exercise price or strike price is the price at which the option can be exercised. The date on which the option can no longer be exercised is called the expiration date.
]
#example[
  The buyer of a crude oil October 21 call on the New York Mercantile Exchange has the right to take a long position in one October crude oil futures contract for 1,000 barrels (determined by the exchange) at a price of \$21 per barrel (strike price) on or before October (expiration date).
]

== Exercise and Assignment
A trader who intends to exercise an option must submit an exercise notice to either the seller of the option, if purchased from a dealer, or to the guarantor of the option, if purchased on the exchange.

An option can also be further identified by its conditions of exercise. An _American_ option is one that can be exercised at any time on or before the expiration date. A _European_ option, on the other hand, can only be exercised on the expiration date. The great majority of exchange-traded options are American options.

An option's premium comprises of two values: intrinsic and extrinsic. The intrinsic value is the difference between the underlying price and the strike price. For example, if gold is currently trading at \$450 per ounce and there exists a 400 call option, the intrinsic value of the option is \$50 per ounce. Conversely, if a stock is trading at \$100 and there exists a 105 put option, the intrinsic value of the option is \$5 per share. 

When the intrinsic value is greater than zero, we say that it is "in the money." For example, the 400 call option on gold is 50 in the money.

The extrinsic value of an option is also called the time value. It seems like there is no exact way to quanitfy extrinsic value, except for that it is the difference in the premium between the option and the intrinsic value. For example, if gold is trading at \$450 per ounce and there exists a 400 call option going at \$65, the extrinsic value of the option is \$15 per ounce. 

An option whose exercise price is identical to the current price of the underlying is said to be "at the money."

== Market Integrity
It is important that the trades that people make actually occur. One example is that the trader must have access to capital that is at least equal to an option's intrinsic value.

If a trader cannot fulfill the terms of the contract, the responsibilty falls to the trader's clearing firm, which is a member firm of the exchange which process trades made by an individual and which grees to fulfill any financial obligation arising from those trades. No individual is allowed to trade on an exchange without first becoming associated with a clearing firm.

== Margin Requirements
Traders will often have to put a type of deposit in with the clearing house that gives them permission to trade on the associated exchange. This ensures that if the market moves adversely, the trader will still be able to fulfill any future financial obligations resulting from the trade.

== Settlment Procedures
New option traders can be confused because different exchanges use different methods of settlement. 

*Stock-type settlment*: Suppose you buy 100 shares of a stock at a strike price of \$50. The value of the stock is \$5,000. Now suppose the stock rises to \$60 per share, and the owner of the stock will show a \$10 profit per share. This means he gains \$1,000, but even so, he won't be able to actually spend \$1,000 until he formally liquidates the position by selling the 100 shares at a price of \$60 per share. This type of settlement procedure, where purchase requires full and immediate payment, and where profits or losses are unrealized until the position is liquidated, is called stock-type settlement.

*Future-type settlment*: On the other hand, futures type settlement requires no initial cash payment from the buyer to the seller. Moreover, all profits and losses are immediately realized, even if the position is not liquidated. If a trader buys a gold features contract covering 100 ounces of gold at \$450 per ounce, the full value of the contract is \$45,000. The buyer, however, is not required to pay the seller the full \$45,000 value of the contract. The buyer doesn't have to pay any money at all. At the end of each trading day, the buyer and the seller will immediately realize any profits or losses resulting from movement in the price of the original gold futures contract. Rises from \$450 to \$470 per ounce, then \$2,000 will be credited to teh buyer's account, and he will have immediate use of these funds even if he does not liquidate the position.

If the price drops instead, he will realized an immediate loss of \$2,000. If he does not have sufficient funds in his account to cover the loss, the clearing house will issue a variation call. 

#definition[
  A variation call is a demand for the trader to deposit additional margin to cover the loss in the value of the position.
]
#definition[
  A long underlying position, a trader will profit if the prices rise and lose if the prices fall. Vice versa for a short underlying position. This terminology carries over to option market. THe terms long and short refer to the purchase or sale of a contract. 
]

= Elementary Strategies
A new trader may have to deal with something like 30 different options when they start working. They could be looking a calls and puts of 5 different stocks that each have 6 expiration dates or something like that. That's why it can be a little intimidating to start out with options trading. 

For awhile, a junior trader may focus on trading one or two types of options at a time but over time they'll learn how they can used mixed strategies to take advantage of all the different options they have at their disposal. 
== Simple Buy and Sell Strategies
Consider the price of calls and puts for a certain stock at a given expiration date as depicted below.
#set align(center)
#table(
  columns: 8,
  [], [*85*], [*90*], [*95*], [*100*], [*105*], [*110*], [*115*],
  [Calls], [14.05], [9.35], [5.50], [2.70], [1.15], [0.45], [0.20],
  [Puts], [0.10], [0.45], [1.55], [3.70],  [7.10], [11.35], [16.10]
)
#set align(left)
What happens when we think that the stock will rise to a price of 108 before the expiration date? Maybe we'll buy a call at 100 for 2.70. Let's say at the time of expiration, the stock is in fact a 108 exactly. This means we'll get a net profit of
$
  (108 - 100) - 2.70 = 5.30.
$
Similarly, if we purchased any of the other calls at $<= 105$, then we would have profited as the intrinsic price of the option will be greater than what the depicted market says. As for the 110 and 115 calls, if we think the stock will settle at 108, then regardless of the price, we would prefer to be sellers of the calls rather than buyers. So if someone buys a 115 call from us at a price of 0.20, we would have profited by exactly that premium at the time of expiration. 

We can approach puts very similarly. If we believe the price will end up at 108, then buying any put $<= 105$ will again be useless. As such, we would like to sell these and profit based on the premium. As for the 110 and 115 puts, it's true that we would be more inclined to purchase these. However, if we look at their pricing, it seems that they are overvalued on the market. Suppose we bought a 115 put at a price of 16.10. Our profit would then be 
$
  (115 - 108) - 16.10 < 0.
$
As such, we would actually end up losing money. This means that we would actually want to sell these puts as well. For example, if we sold the same 115 put at 16.10, then our profit would be 
$
  16.10 - (115 - 108) = 9.10.
$
This is because we need to account for the fact that if we had kept the put, then we would have profited by $115 - 108 = 7$ dollars.

Of course, these values would all be very different if we had a different assumption about the underlying price. The decisions we would make would different, for example, if we thought the underlying price would fall to be below 90, or raise to 120.

One may ask why we would even play with options, a derviative of the underlying stock, instead of buying/selling the the stock itself. This can be answered by showing profit/loss curves of buying at certain prices veruss buying calls/puts at certain prices. I'm too lazy to add diagrams to these notes for now, but the TL;DR is that profit and loss are both technically unlimited when playing with the underlying stock. However, with options, the loss is actually capped at the premium (since we aren't forced to exercise the contract), while the profit remains theoretically unlimited.
#remark[
  The graph of the option profit/loss looks like a RELU function.
]

== Risk/Reward Characteristics
As a recap of the last section, being long calls/puts has unlimited upside potential while having finite and limited downside potential. The point at which we are at a minimum profit is exactly when we choose to not exercise the call/put that we obtained, meaning we just lose the premium that we originally paid. However, selling these options will have this flipped; selling calls/puts have limited upside and unlimited downside. Instead of saying upside/downside, we'll instead say reward/risk respectively.

This may causee a new trader to question while anyone sells options. But like, people do, so there must be a reason. The answer to this is that while the risk is unlimited, the probability of the risk happening is pretty low.

To draw a parallel, suppose someone comes up to you with a fair coin. If you guess the coin after he flips it, you double your life savings. If you don't, you lose everything. Most people probably wouldn't flip the coin, which is extremely rational. But what if instead he came up with a coin that came up with heads 99.9999\% of the time? Well then you would of course take the deal and just guess heads. 

This just means that the probability of going very wrong when selling options at the right time is so low that we basically don't even consider it.

== Combination Strategies
Suppose we buy a call _and_ a put at 2.70 and 3.70 respectively. We have paid a total price of 6.40, which is our theoretic max loss. However, we only hit this max loss if the stock settles at exactly 100. If it is any amount above 100, then our call will profit and our put will be useless and vice versa. However, to profit overall, we would need our underlying stock to end up outside the interval $[100 - 6.40, 100 + 6.40]$. Outside of this range, the potential profit is unlimited.


= Introduction to Theoretical Pricing Models
One important thing to consider is that when you buy an option, the fact that you're bullish on the underlying doesn't mean everything. It's possible that someone who buys an option can it be correct that the underlying will tend to the direction that he wants, but it may not do it as fast as he expected. 

== Word About Models
The thing about models is that they make some assumptions about the real world in order to make a model. Models are not meant to exactly replicate what happens in the real world, but at least be a close approximation. This can mean something some sort of construction of a real airplane that you see in a museum or a mathmematical model.

In options pricing, one famous equation is the Black-Scholes model. Black Scholes is used for European options where we have the assumption that no early exercise is permitted on non-dividend paying stocks. However, after its introduction, people realized that most stocks do pay dividends, so they added a dividend component. It may seem that Black Scholes, with its assumption of no early exercise, is poorly suited for most markets. However, it has proven so easy to use that many traders do not believe the more accurate values derived from an American option pricing model, which allows for the possibility of early exercise, is worth the additional effort. 

There are different versions of the model, and it is worth making a few comments about these differences. 

== Black-Scholes Model
The values needed for Black-Scholes are 
1. The option's exercise price.
2. The amount of time remaining to expiration. 
3. The current price of the underlying contract. 
4. The risk-free interest rate over the life of the option. 
5. The volatility of the underlying contract. 

The current price of the underlying contract is hard to define because at any given time, there is going to be a bid and ask price. Which one we use depends on whether we are long or short. 

The hardest part here to quantify is volatility, so we will dedicate a whole chapter to doing that.

= Volatility