import React, { useState } from "react";

import Button from "@mui/material/Button";
import BackupTable from "@mui/icons-material/BackupTable";
import TableChart from "@mui/icons-material/TableChart";
import ZoomOutMapIcon from "@mui/icons-material/ZoomOutMap";
import InfoIcon from "@mui/icons-material/Info";
import { ArrowDropDown, ArrowDropUp } from "@mui/icons-material";

import { styled } from "@mui/material";

const ChartButtonWrapper = styled("div")`
    display: flex;
    flex-direction: column;
    gap: 15px;

    .chart-button {
        height: 36px;
        width: 36px !important;
        background-color: #f4f4f4 !important;
        color: #333 !important;
        border-radius: 20px;

        svg {
            height: 100%;
            width: 100%;
        }
    }
`;

const ChartButtons = (props) => {
    const [displayChartOptions, toggleChartOptions] = useState(true);

    const {
        chartButtons: {
            displayHelp,
            displayPopupTable,
            displayQuickChange,
            displayDownload,
        },
        maxChartID = null,
        isToggled = false,
        chartTypes,
        showInfoModal,
        showMaxviewModal,
        showHelpModal,
        toggleDataview,
        untoggleDataview,
        dataviewToggle,
        currentChartID,
    } = props;

    const handleOptionsToggle = () => {
        if (displayChartOptions === false) {
            toggleChartOptions(true);
        } else {
            toggleChartOptions(false);
        }
    };

    return (
        <ChartButtonWrapper>
            {!displayChartOptions ? (
                <Button
                    className="chart-buttons"
                    title="Show Chart Options"
                    variant="contained"
                    onClick={handleOptionsToggle}
                >
                    <ArrowDropDown />
                </Button>
            ) : (
                <Button
                    className="chart-buttons"
                    title="Minimize Chart Options"
                    variant="contained"
                    onClick={handleOptionsToggle}
                >
                    <ArrowDropUp />
                </Button>
            )}

            {displayChartOptions === true && (
                <>
                    {displayHelp ? (
                        <Button
                            className="chart-buttons"
                            title="Show Help Text"
                            variant="contained"
                            onClick={() => showHelpModal()}
                        >
                            <InfoIcon />
                        </Button>
                    ) : null}

                    {displayPopupTable ? (
                        <Button
                            title="Detailed Data"
                            variant="contained"
                            onClick={() => showInfoModal()}
                            className="chart-buttons"
                        >
                            <BackupTable />
                        </Button>
                    ) : null}

                    {displayQuickChange ? (
                        <>
                            {dataviewToggle === false && (
                                <Button
                                    title="Change View"
                                    variant="contained"
                                    onClick={() => toggleDataview()}
                                    className="chart-buttons"
                                >
                                    <TableChart />
                                </Button>
                            )}
                            {dataviewToggle === true && (
                                <Button
                                    title="Change View"
                                    variant="contained"
                                    onClick={() => untoggleDataview()}
                                    className="chart-buttons"
                                >
                                    <i className="material-icons">
                                        insert_chart_outlined
                                    </i>
                                </Button>
                            )}
                        </>
                    ) : null}

                    {maxChartID ? (
                        <Button
                            title="Max View"
                            variant="contained"
                            onClick={() => showMaxviewModal()}
                            className="chart-buttons"
                        >
                            <ZoomOutMapIcon />
                        </Button>
                    ) : null}

                    {displayDownload
                        ? {
                              /* <DownloadChart
                            isContainer={chartTypes === "container"}
                            isKPI={chartTypes === "KPI"}
                            isTable={chartTypes === "table"}
                            isToggled={isToggled}
                            isMax={false}
                            exportChartID={currentChartID}
                            chartTypes={chartTypes}
                            isMap={props.isMap}
                            {...props}
                        /> */
                          }
                        : null}
                </>
            )}
        </ChartButtonWrapper>
    );
};

export default ChartButtons;
