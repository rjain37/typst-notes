#set heading(numbering: "1.")
#set enum(numbering: "1.a)")

#import "@preview/ilm:1.4.0": *
#import "../preamble.typ" : *
#show: thmrules

#show: ilm.with(
  title: [Natenburg],
  author: "Rohan Jain",
  date: datetime(year: 2024, month: 03, day: 19),
  preface: [
    #align(center + horizon)[
      Put-call-parity more like phencyclidine
    ]
  ],
  table-of-contents: none,
)

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