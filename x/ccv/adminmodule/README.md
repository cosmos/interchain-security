# Admin module
This module allows admin accounts to submit governance proposals that will be immediately executed in the first EndBlock. 

Originally, this module is taken from the [Composer repository](https://github.com/cosmos/composer).
All credit and thanks go to the original authors.

To enable provider driven governance of interchain security, some modifications have been made in EndBlocker. The interchain account of the provider's governance module should be able to submit proposals to the admin module on the consumer chain side. To achieve this, the interchain account address of the provider's governance module is added as an admin in the EndBlocker of the admin module.
Also, separate whitelists are introduced to specify which types of proposals are allowed to be submitted by provider's governance module admin and all other admins from the consumer chain.