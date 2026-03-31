## Quick TODO list

## Node tip display

Show the last 2 hex digits of the node hash to ensure they are all one
the *same* block at that number.

## Console <div> in <p> error

￼installHook.js:1 In HTML, <div> cannot be a descendant of <p>.
This will cause a hydration error.

  ...
    <Styled(div) as="div" ref={null} className="MuiBox-root" theme={{...}} sx={{p:2, ...}}>
      <Insertion6>
      <div className="MuiBox-roo...">
        <NodeInspector nodeId="node-4">
          <Box3>
            <Styled(div) as="div" ref={null} className="MuiBox-root" theme={{...}} sx={{}}>
              <Insertion6>
              <div className="MuiBox-roo...">
                <Typography2>
                <Box3 sx={{mb:1}}>
                  <Styled(div) as="div" ref={null} className="MuiBox-root" theme={{...}} sx={{mb:1}}>
                    <Insertion6>
                    <div className="MuiBox-roo...">
                      <Typography2>
                      <Typography2>
                      <Typography2>
                      <Typography2>
                      <Typography2>
                      <Divider2>
                      <Typography2>
                      <Box3 sx={{ml:1,mb:0.5}}>
                        <Styled(div) as="div" ref={null} className="MuiBox-root" theme={{...}} sx={{ml:1,mb:0.5}}>
                          <Insertion6>
                          <div className="MuiBox-roo...">
                            <Typography2 variant="body2" fontSize={11}>
                              <MuiTypography-root as="p" ref={null} className="MuiTypogra..." sx={{fontSize:11, ...}} ...>
                                <Insertion6>
>                               <p
>                                 className="MuiTypography-root MuiTypography-body2 css-1u8ahwx-MuiTypography-root"
>                                 style={{}}
>                               >
                                  <Chip2 label="Duplex" size="small" sx={{mr:0.5,height:16, ...}}>
                                    <MuiChip-root as="div" className="MuiChip-ro..." disabled={undefined} ...>
                                      <Insertion6>
>                                     <div
>                                       className="MuiChip-root MuiChip-filled MuiChip-sizeSmall MuiChip-colorDefault ..."
>                                       disabled={undefined}
>                                       onClick={undefined}
>                                       onKeyDown={function handleKeyDown}
>                                       onKeyUp={function handleKeyUp}
>                                       tabIndex={undefined}
>                                       ref={function}
>                                     >

## Consensus

We need to implement true Praos consensus (longest chain).  I suspect
the co-ordinator may be doing too much in this regard and should delegate
the choice of blocks to fetch entirely to the node's consensus.

Consensus will need to build a tree of chains / forks and when a new block
is offered, attach it to the relevant fork (this requires the previous block
hash from the header).  Then it should choose which of the chains is now
the longest, and fetch blocks it does not already have.

## Reordering of events

It looks like events are getting re-ordered in the log, or lost - for example 
you see a VTBundleGenerated before EBGenerated or EBReceived.

Actually there are cases of VTBundleGenerated with no EB traffic before it at
all.  This must be a case of lost events I think.

